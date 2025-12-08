use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;
use std::sync::{Arc, Mutex, mpsc};

use simple_loader::smf::{
    hash_name, Arch, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SMF_FLAG_EXECUTABLE, SMF_MAGIC, SECTION_FLAG_EXEC, SECTION_FLAG_READ,
};
use simple_parser::ast::{
    AssignOp, BinOp, Block, ClassDef, ConstStmt, ContextStmt, Expr, ExternDef, FStringPart, FunctionDef, IfStmt, LambdaParam,
    MatchStmt, Node, Pattern, PointerKind, StaticStmt, Type, UnaryOp,
};
use simple_common::gc::GcAllocator;
use simple_common::manual::{ManualGc, Unique as ManualUnique};
use simple_runtime::concurrency::{self, ActorHandle, Message};
use simple_type::check as type_check;
// Type checking lives in the separate crate simple-type
use tracing::instrument;
use thiserror::Error;

/// Variable environment for compile-time evaluation
type Env = HashMap<String, Value>;

thread_local! {
    static MANUAL_GC: ManualGc = ManualGc::new();
}

#[derive(Debug)]
enum Value {
    Int(i64),
    Bool(bool),
    Str(String),
    Symbol(String),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Dict(HashMap<String, Value>),
    Lambda { params: Vec<String>, body: Box<Expr>, env: Env },
    Object { class: String, fields: HashMap<String, Value> },
    Enum { enum_name: String, variant: String, payload: Option<Box<Value>> },
    Actor(ActorHandle),
    Unique(ManualUniqueValue),
    Nil,
}

impl Value {
    fn as_int(&self) -> Result<i64, CompileError> {
        match self {
            Value::Int(i) => Ok(*i),
            Value::Bool(b) => Ok(if *b { 1 } else { 0 }),
            Value::Unique(u) => u.inner().as_int(),
            Value::Str(_) => Err(CompileError::Semantic("expected int, got string".into())),
            Value::Symbol(_) => Err(CompileError::Semantic("expected int, got symbol".into())),
            Value::Nil => Ok(0),
            other => Err(CompileError::Semantic(format!(
                "expected int, got {other:?}"
            ))),
        }
    }

    fn to_key_string(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => s.clone(),
            Value::Unique(u) => u.inner().to_key_string(),
            Value::Nil => "nil".to_string(),
            other => format!("{other:?}"),
        }
    }

    fn truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Str(s) => !s.is_empty(),
            Value::Symbol(_) => true,
            Value::Array(a) => !a.is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            Value::Dict(d) => !d.is_empty(),
            Value::Nil => false,
            Value::Unique(u) => u.inner().truthy(),
            Value::Object { .. } | Value::Enum { .. } | Value::Lambda { .. } | Value::Actor(_) => true,
        }
    }

    fn to_display_string(&self) -> String {
        match self {
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => format!(":{s}"),
            Value::Int(i) => i.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Array(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("({})", parts.join(", "))
            }
            Value::Dict(map) => {
                let parts: Vec<String> = map.iter().map(|(k, v)| format!("{}: {}", k, v.to_display_string())).collect();
                format!("{{{}}}", parts.join(", "))
            }
            Value::Nil => "nil".into(),
            Value::Unique(u) => format!("&{}", u.inner().to_display_string()),
            other => format!("{other:?}"),
        }
    }

    /// Convert a unique pointer into its inner value (clone) for read-only operations.
    fn deref_unique(self) -> Value {
        match self {
            Value::Unique(u) => u.into_inner(),
            other => other,
        }
    }
}

#[derive(Debug)]
struct ManualUniqueValue {
    ptr: ManualUnique<Value>,
}

impl ManualUniqueValue {
    fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self { ptr: gc.alloc(value) })
    }

    fn inner(&self) -> &Value {
        &self.ptr
    }

    fn into_inner(self) -> Value {
        self.ptr.into_inner()
    }
}

impl Clone for ManualUniqueValue {
    fn clone(&self) -> Self {
        // Cloning a unique pointer duplicates the underlying value into a fresh unique owner.
        Self::new((*self.ptr).clone())
    }
}

impl PartialEq for ManualUniqueValue {
    fn eq(&self, other: &Self) -> bool {
        self.inner() == other.inner()
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::Int(i) => Value::Int(*i),
            Value::Bool(b) => Value::Bool(*b),
            Value::Str(s) => Value::Str(s.clone()),
            Value::Symbol(s) => Value::Symbol(s.clone()),
            Value::Array(a) => Value::Array(a.clone()),
            Value::Tuple(t) => Value::Tuple(t.clone()),
            Value::Dict(d) => Value::Dict(d.clone()),
            Value::Lambda { params, body, env } => Value::Lambda {
                params: params.clone(),
                body: body.clone(),
                env: env.clone(),
            },
            Value::Object { class, fields } => Value::Object { class: class.clone(), fields: fields.clone() },
            Value::Enum { enum_name, variant, payload } => Value::Enum {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
                payload: payload.clone(),
            },
            Value::Actor(handle) => Value::Actor(handle.clone()),
            Value::Unique(u) => Value::Unique(u.clone()),
            Value::Nil => Value::Nil,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
            (Value::Lambda { params: pa, body: ba, env: ea }, Value::Lambda { params: pb, body: bb, env: eb }) => {
                pa == pb && ba == bb && ea == eb
            }
            (Value::Object { class: ca, fields: fa }, Value::Object { class: cb, fields: fb }) => ca == cb && fa == fb,
            (Value::Enum { enum_name: ea, variant: va, payload: pa }, Value::Enum { enum_name: eb, variant: vb, payload: pb }) => {
                ea == eb && va == vb && pa == pb
            }
            (Value::Actor(_), Value::Actor(_)) => true,
            (Value::Unique(a), Value::Unique(b)) => a == b,
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}

thread_local! {
    static ACTOR_INBOX: RefCell<Option<Arc<Mutex<mpsc::Receiver<Message>>>>> = RefCell::new(None);
    static ACTOR_OUTBOX: RefCell<Option<mpsc::Sender<Message>>> = RefCell::new(None);
    static CONST_NAMES: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
    static EXTERN_FUNCTIONS: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
    /// Current context object for context blocks (DSL support)
    static CONTEXT_OBJECT: RefCell<Option<Value>> = RefCell::new(None);
}

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    gc: Option<Arc<dyn GcAllocator>>,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self { gc: None })
    }

    pub fn with_gc(gc: Arc<dyn GcAllocator>) -> Result<Self, CompileError> {
        Ok(Self { gc: Some(gc) })
    }

    /// Compile a Simple source file to an SMF at `out`.
    ///
    /// Currently supports `main = <integer>` which returns the integer value.
    #[instrument(skip(self, source_path, out))]
    pub fn compile(&mut self, source_path: &Path, out: &Path) -> Result<(), CompileError> {
        let source =
            fs::read_to_string(source_path).map_err(|e| CompileError::Io(format!("{e}")))?;

        // Parse to ensure the source is syntactically valid.
        let mut parser = simple_parser::Parser::new(&source);
        let module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // Type inference/checking (features #13/#14 scaffolding)
        type_check(&module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Extract the main function's return value
        let main_value = evaluate_module(&module.items)?;

        write_smf_with_return_value(out, main_value, self.gc.as_ref()).map_err(|e| CompileError::Io(format!("{e}")))
    }
}

/// Stores enum definition: name -> list of variant names
type Enums = HashMap<String, Vec<String>>;

/// Stores impl block methods: type_name -> list of methods
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Stores extern function declarations: name -> definition
type ExternFunctions = HashMap<String, ExternDef>;

/// Evaluate the module and return the `main` binding as an i32.
#[instrument(skip(items))]
fn evaluate_module(items: &[Node]) -> Result<i32, CompileError> {
    // Clear const names and extern functions from previous runs
    CONST_NAMES.with(|cell| cell.borrow_mut().clear());
    EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().clear());

    let mut env = Env::new();
    let mut functions: HashMap<String, FunctionDef> = HashMap::new();
    let mut classes: HashMap<String, ClassDef> = HashMap::new();
    let mut enums: Enums = HashMap::new();
    let mut impl_methods: ImplMethods = HashMap::new();
    let mut extern_functions: ExternFunctions = HashMap::new();

    for item in items {
        match item {
            Node::Function(f) => {
                functions.insert(f.name.clone(), f.clone());
            }
            Node::Struct(s) => {
                env.insert(
                    s.name.clone(),
                    Value::Object {
                        class: s.name.clone(),
                        fields: HashMap::new(),
                    },
                );
            }
            Node::Enum(e) => {
                let variants: Vec<String> = e.variants.iter().map(|v| v.name.clone()).collect();
                enums.insert(e.name.clone(), variants);
            }
            Node::Class(c) => {
                classes.insert(c.name.clone(), c.clone());
                env.insert(
                    c.name.clone(),
                    Value::Object {
                        class: c.name.clone(),
                        fields: HashMap::new(),
                    },
                );
            }
            Node::Impl(impl_block) => {
                // Extract the type name from the target type
                let type_name = get_type_name(&impl_block.target_type);
                // Add all methods from this impl block to the type
                let methods = impl_methods.entry(type_name).or_insert_with(Vec::new);
                for method in &impl_block.methods {
                    methods.push(method.clone());
                }
            }
            Node::Extern(ext) => {
                // Store extern function declaration
                extern_functions.insert(ext.name.clone(), ext.clone());
                // Register in thread-local for call resolution
                EXTERN_FUNCTIONS.with(|cell| cell.borrow_mut().insert(ext.name.clone()));
            }
            Node::Let(_) | Node::Const(_) | Node::Static(_) | Node::Assignment(_) | Node::If(_) | Node::For(_) | Node::While(_) | Node::Loop(_) | Node::Match(_) | Node::Context(_) => {
                if let Control::Return(val) = exec_node(item, &mut env, &functions, &classes, &enums, &impl_methods)? {
                    // Early return sets main implicitly
                    return val.as_int().map(|v| v as i32);
                }
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let val = evaluate_expr(expr, &env, &functions, &classes, &enums, &impl_methods)?;
                    return val.as_int().map(|v| v as i32);
                }
                return Ok(0);
            }
            Node::Expression(expr) => {
                // Handle functional update operator at top level
                if let Expr::FunctionalUpdate { target, method, args } = expr {
                    if let Expr::Identifier(name) = target.as_ref() {
                        // Check if this is a const (immutable) name
                        let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                        if is_const {
                            return Err(CompileError::Semantic(format!("cannot use functional update on const '{name}'")));
                        }
                        // Get current value
                        let recv_val = env.get(name).cloned().ok_or_else(|| {
                            CompileError::Semantic(format!("undefined variable: {name}"))
                        })?;
                        // Call the method
                        let method_call = Expr::MethodCall {
                            receiver: Box::new(Expr::Identifier(name.clone())),
                            method: method.clone(),
                            args: args.clone(),
                        };
                        let result = evaluate_expr(&method_call, &env, &functions, &classes, &enums, &impl_methods)?;
                        // Assign result back if same type
                        let new_value = match (&recv_val, &result) {
                            (Value::Array(_), Value::Array(_)) => result,
                            (Value::Dict(_), Value::Dict(_)) => result,
                            (Value::Str(_), Value::Str(_)) => result,
                            (Value::Tuple(_), Value::Tuple(_)) => result,
                            (Value::Object { .. }, Value::Object { .. }) => result,
                            _ => env.get(name).cloned().unwrap_or(recv_val),
                        };
                        env.insert(name.clone(), new_value);
                        continue;
                    }
                    return Err(CompileError::Semantic("functional update target must be an identifier".into()));
                }
                let _ = evaluate_expr(expr, &env, &functions, &classes, &enums, &impl_methods)?;
            }
            _ => {}
        }
    }

    let main_val = env
        .get("main")
        .cloned()
        .unwrap_or(Value::Int(0))
        .as_int()? as i32;
    Ok(main_val)
}

/// Extract type name from a Type AST node
fn get_type_name(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        _ => "unknown".to_string(),
    }
}

fn write_smf_with_return_value(
    path: &Path,
    return_value: i32,
    gc: Option<&Arc<dyn GcAllocator>>,
) -> std::io::Result<()> {
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = std::mem::size_of::<SmfSection>() as u64;
    let code_offset = section_table_offset + section_table_size;

    // Generate x86-64 code to return the value
    // mov eax, imm32 = B8 + 4 bytes (little-endian)
    // ret = C3
    let code_bytes = {
        let mut code = Vec::with_capacity(6);
        code.push(0xB8u8); // mov eax, imm32
        code.extend_from_slice(&return_value.to_le_bytes());
        code.push(0xC3); // ret
        code
    };
    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(&code_bytes);
    }
    let symbol_table_offset = code_offset + code_bytes.len() as u64;

    let mut header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: simple_loader::smf::Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        reserved: [0; 8],
    };

    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    let code_section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    };

    let string_table = b"main\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    };

    header.symbol_table_offset = symbol_table_offset;

    let mut buf = Vec::new();
    push_struct(&mut buf, &header);
    push_struct(&mut buf, &code_section);
    buf.extend_from_slice(&code_bytes);
    push_struct(&mut buf, &symbol);
    buf.extend_from_slice(&string_table);

    fs::write(path, buf)
}

fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let bytes =
        unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) };
    buf.extend_from_slice(bytes);
}

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("io: {0}")]
    Io(String),
    #[error("parse: {0}")]
    Parse(String),
    #[error("semantic: {0}")]
    Semantic(String),
}

/// Control flow for statement execution.
enum Control {
    Next,
    Return(Value),
    Break(Option<Value>),
    Continue,
}

fn exec_node(
    node: &Node,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    match node {
        Node::Let(let_stmt) => {
            if let Some(value_expr) = &let_stmt.value {
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                if let Pattern::Identifier(name) = &let_stmt.pattern {
                    env.insert(name.clone(), value);
                    // Track immutable bindings (let without mut)
                    if !let_stmt.is_mutable {
                        CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                    }
                } else if let Pattern::MutIdentifier(name) = &let_stmt.pattern {
                    // Mutable binding via pattern
                    env.insert(name.clone(), value);
                } else if let Pattern::Tuple(patterns) = &let_stmt.pattern {
                    // Destructure tuple
                    if let Value::Tuple(values) = value {
                        for (pat, val) in patterns.iter().zip(values.into_iter()) {
                            if let Pattern::Identifier(name) = pat {
                                env.insert(name.clone(), val);
                                if !let_stmt.is_mutable {
                                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                                }
                            } else if let Pattern::MutIdentifier(name) = pat {
                                env.insert(name.clone(), val);
                            }
                        }
                    }
                } else if let Pattern::Array(patterns) = &let_stmt.pattern {
                    // Destructure array
                    if let Value::Array(values) = value {
                        for (pat, val) in patterns.iter().zip(values.into_iter()) {
                            if let Pattern::Identifier(name) = pat {
                                env.insert(name.clone(), val);
                                if !let_stmt.is_mutable {
                                    CONST_NAMES.with(|cell| cell.borrow_mut().insert(name.clone()));
                                }
                            } else if let Pattern::MutIdentifier(name) = pat {
                                env.insert(name.clone(), val);
                            }
                        }
                    }
                }
            }
            Ok(Control::Next)
        }
        Node::Const(const_stmt) => {
            let value = evaluate_expr(&const_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(const_stmt.name.clone(), value);
            CONST_NAMES.with(|cell| cell.borrow_mut().insert(const_stmt.name.clone()));
            Ok(Control::Next)
        }
        Node::Static(static_stmt) => {
            let value = evaluate_expr(&static_stmt.value, env, functions, classes, enums, impl_methods)?;
            env.insert(static_stmt.name.clone(), value);
            // Static without mut is also immutable
            if !static_stmt.is_mutable {
                CONST_NAMES.with(|cell| cell.borrow_mut().insert(static_stmt.name.clone()));
            }
            Ok(Control::Next)
        }
        Node::Assignment(assign) if assign.op == AssignOp::Assign => {
            if let Expr::Identifier(name) = &assign.target {
                // Check if this is a const (immutable) name
                let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                if is_const {
                    return Err(CompileError::Semantic(format!("cannot assign to const '{name}'")));
                }
                let value = evaluate_expr(&assign.value, env, functions, classes, enums, impl_methods)?;
                env.insert(name.clone(), value);
                Ok(Control::Next)
            } else {
                Err(CompileError::Semantic("unsupported assignment target".into()))
            }
        }
        Node::If(if_stmt) => exec_if(if_stmt, env, functions, classes, enums, impl_methods),
        Node::While(while_stmt) => exec_while(while_stmt, env, functions, classes, enums, impl_methods),
        Node::Loop(loop_stmt) => exec_loop(loop_stmt, env, functions, classes, enums, impl_methods),
        Node::For(for_stmt) => exec_for(for_stmt, env, functions, classes, enums, impl_methods),
        Node::Return(ret) => {
            let value = if let Some(expr) = &ret.value {
                evaluate_expr(expr, env, functions, classes, enums, impl_methods)?
            } else {
                Value::Nil
            };
            Ok(Control::Return(value))
        }
        Node::Break(b) => {
            let value = if let Some(expr) = &b.value {
                Some(evaluate_expr(expr, env, functions, classes, enums, impl_methods)?)
            } else {
                None
            };
            Ok(Control::Break(value))
        }
        Node::Continue(_) => Ok(Control::Continue),
        Node::Match(match_stmt) => exec_match(match_stmt, env, functions, classes, enums, impl_methods),
        Node::Context(ctx_stmt) => exec_context(ctx_stmt, env, functions, classes, enums, impl_methods),
        Node::Expression(expr) => {
            // Handle functional update operator: obj->method(args) desugars to obj = obj.method(args)
            if let Expr::FunctionalUpdate { target, method, args } = expr {
                if let Expr::Identifier(name) = target.as_ref() {
                    // Check if this is a const (immutable) name
                    let is_const = CONST_NAMES.with(|cell| cell.borrow().contains(name));
                    if is_const {
                        return Err(CompileError::Semantic(format!("cannot use functional update on const '{name}'")));
                    }
                    // Get current value
                    let recv_val = env.get(name).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("undefined variable: {name}"))
                    })?;
                    // Call the method - create a temporary MethodCall expression
                    let method_call = Expr::MethodCall {
                        receiver: Box::new(Expr::Identifier(name.clone())),
                        method: method.clone(),
                        args: args.clone(),
                    };
                    let result = evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)?;
                    // For mutating methods that return the modified collection, use the result
                    // For methods that modify in place and return something else, use the new value
                    // Check if the result is the same type as original - if so, assign it
                    let new_value = match (&recv_val, &result) {
                        (Value::Array(_), Value::Array(_)) => result,
                        (Value::Dict(_), Value::Dict(_)) => result,
                        (Value::Str(_), Value::Str(_)) => result,
                        (Value::Tuple(_), Value::Tuple(_)) => result,
                        (Value::Object { .. }, Value::Object { .. }) => result,
                        // For other cases, re-fetch the variable as it may have been mutated
                        _ => env.get(name).cloned().unwrap_or(recv_val),
                    };
                    env.insert(name.clone(), new_value);
                    return Ok(Control::Next);
                }
                return Err(CompileError::Semantic("functional update target must be an identifier".into()));
            }
            let _ = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            Ok(Control::Next)
        }
        _ => Ok(Control::Next),
    }
}

fn exec_block(
    block: &Block,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    for stmt in &block.statements {
        match exec_node(stmt, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            flow @ (Control::Return(_) | Control::Break(_) | Control::Continue) => return Ok(flow),
        }
    }
    Ok(Control::Next)
}

fn exec_if(
    if_stmt: &IfStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    if evaluate_expr(&if_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
        return exec_block(&if_stmt.then_block, env, functions, classes, enums, impl_methods);
    }
    for (cond, block) in &if_stmt.elif_branches {
        if evaluate_expr(cond, env, functions, classes, enums, impl_methods)?.truthy() {
            return exec_block(block, env, functions, classes, enums, impl_methods);
        }
    }
    if let Some(block) = &if_stmt.else_block {
        return exec_block(block, env, functions, classes, enums, impl_methods);
    }
    Ok(Control::Next)
}

fn exec_while(
    while_stmt: &simple_parser::ast::WhileStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        if !evaluate_expr(&while_stmt.condition, env, functions, classes, enums, impl_methods)?.truthy() {
            break;
        }
        match exec_block(&while_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

fn exec_loop(
    loop_stmt: &simple_parser::ast::LoopStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    loop {
        match exec_block(&loop_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

/// Execute a context block - sets implicit receiver for method calls
fn exec_context(
    ctx_stmt: &ContextStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    // Evaluate the context expression
    let context_obj = evaluate_expr(&ctx_stmt.context, env, functions, classes, enums, impl_methods)?;

    // Save the previous context (if any) for nesting
    let prev_context = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());

    // Set the new context
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = Some(context_obj));

    // Execute the body
    let result = exec_block(&ctx_stmt.body, env, functions, classes, enums, impl_methods);

    // Restore previous context
    CONTEXT_OBJECT.with(|cell| *cell.borrow_mut() = prev_context);

    result
}

fn exec_for(
    for_stmt: &simple_parser::ast::ForStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let iterable = evaluate_expr(&for_stmt.iterable, env, functions, classes, enums, impl_methods)?;
    let items = match iterable {
        Value::Object { class, fields } if class == "__range__" => {
            if let Some(Value::Int(start)) = fields.get("start") {
                if let Some(Value::Int(end)) = fields.get("end") {
                    let inclusive = matches!(fields.get("inclusive"), Some(Value::Bool(true)));
                    let mut v = Vec::new();
                    let mut i = *start;
                    if inclusive {
                        while i <= *end {
                            v.push(i);
                            i += 1;
                        }
                    } else {
                        while i < *end {
                            v.push(i);
                            i += 1;
                        }
                    }
                    v
                } else {
                    return Err(CompileError::Semantic("invalid range".into()));
                }
            } else {
                return Err(CompileError::Semantic("invalid range".into()));
            }
        }
        Value::Object { class, fields } if class == "__array__" => {
            let mut out = Vec::new();
            for (_, v) in fields {
                if let Value::Int(i) = v {
                    out.push(i);
                }
            }
            out
        }
        _ => return Err(CompileError::Semantic("for expects range or array".into())),
    };

    for val in items {
        if let Pattern::Identifier(name) = &for_stmt.pattern {
            env.insert(name.clone(), Value::Int(val));
        }
        match exec_block(&for_stmt.body, env, functions, classes, enums, impl_methods)? {
            Control::Next => {}
            Control::Continue => continue,
            Control::Break(_) => break,
            ret @ Control::Return(_) => return Ok(ret),
        }
    }
    Ok(Control::Next)
}

fn exec_match(
    match_stmt: &MatchStmt,
    env: &mut Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Control, CompileError> {
    let subject = evaluate_expr(&match_stmt.subject, env, functions, classes, enums, impl_methods)?;

    for arm in &match_stmt.arms {
        let mut bindings = HashMap::new();
        if pattern_matches(&arm.pattern, &subject, &mut bindings, enums)? {
            // Check guard if present
            if let Some(guard) = &arm.guard {
                // Create temporary env with bindings for guard evaluation
                let mut guard_env = env.clone();
                for (name, value) in &bindings {
                    guard_env.insert(name.clone(), value.clone());
                }
                if !evaluate_expr(guard, &guard_env, functions, classes, enums, impl_methods)?.truthy() {
                    continue; // Guard failed, try next arm
                }
            }

            // Apply bindings to environment
            for (name, value) in bindings {
                env.insert(name, value);
            }

            // Execute the arm body
            return exec_block(&arm.body, env, functions, classes, enums, impl_methods);
        }
    }

    // No arm matched - this could be an error in a strict language
    Ok(Control::Next)
}

/// Check if a pattern matches a value, collecting bindings
fn pattern_matches(
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
    enums: &Enums,
) -> Result<bool, CompileError> {
    match pattern {
        Pattern::Wildcard => Ok(true),

        Pattern::Identifier(name) => {
            // Bind the value to this name
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::MutIdentifier(name) => {
            bindings.insert(name.clone(), value.clone());
            Ok(true)
        }

        Pattern::Literal(lit_expr) => {
            // Compare the value with the literal
            match lit_expr.as_ref() {
                Expr::Integer(i) => {
                    if let Value::Int(v) = value {
                        Ok(*v == *i)
                    } else {
                        Ok(false)
                    }
                }
                Expr::String(s) => {
                    if let Value::Str(v) = value {
                        Ok(v == s)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Symbol(sym) => {
                    if let Value::Symbol(v) = value {
                        Ok(v == sym)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Bool(b) => {
                    if let Value::Bool(v) = value {
                        Ok(*v == *b)
                    } else {
                        Ok(false)
                    }
                }
                Expr::Nil => Ok(matches!(value, Value::Nil)),
                _ => Ok(false),
            }
        }

        Pattern::Enum { name: enum_name, variant, payload } => {
            if let Value::Enum { enum_name: ve, variant: vv, payload: value_payload } = value {
                if enum_name == ve && variant == vv {
                    // Both have no payload
                    if payload.is_none() && value_payload.is_none() {
                        return Ok(true);
                    }
                    // Pattern expects payload, value has payload
                    if let (Some(patterns), Some(vp)) = (payload, value_payload) {
                        // For single payload, bind to first pattern
                        if patterns.len() == 1 {
                            if pattern_matches(&patterns[0], vp.as_ref(), bindings, enums)? {
                                return Ok(true);
                            }
                        }
                    }
                    // Pattern expects no payload but value has one (still matches variant)
                    if payload.is_none() && value_payload.is_some() {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }

        Pattern::Tuple(patterns) => {
            if let Value::Tuple(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Array(patterns) => {
            if let Value::Array(values) = value {
                if patterns.len() != values.len() {
                    return Ok(false);
                }
                for (pat, val) in patterns.iter().zip(values.iter()) {
                    if !pattern_matches(pat, val, bindings, enums)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Ok(false)
        }

        Pattern::Struct { name, fields } => {
            if let Value::Object { class, fields: obj_fields } = value {
                if class == name {
                    for (field_name, field_pat) in fields {
                        if let Some(field_val) = obj_fields.get(field_name) {
                            if !pattern_matches(field_pat, field_val, bindings, enums)? {
                                return Ok(false);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Or(patterns) => {
            for pat in patterns {
                let mut temp_bindings = HashMap::new();
                if pattern_matches(pat, value, &mut temp_bindings, enums)? {
                    bindings.extend(temp_bindings);
                    return Ok(true);
                }
            }
            Ok(false)
        }

        Pattern::Typed { pattern, .. } => {
            // For now, ignore the type annotation and just match the pattern
            pattern_matches(pattern, value, bindings, enums)
        }

        Pattern::Rest => {
            // Rest pattern matches anything (used in array/tuple destructuring)
            Ok(true)
        }
    }
}

/// Evaluate a constant expression at compile time
#[instrument(skip(env, functions, classes, enums, impl_methods))]
fn evaluate_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(Value::Int(*value)),
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Nil => Ok(Value::Nil),
        Expr::String(s) => Ok(Value::Str(s.clone())),
        Expr::FString(parts) => {
            let mut out = String::new();
            for part in parts {
                match part {
                    FStringPart::Literal(lit) => out.push_str(lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        out.push_str(&v.to_display_string());
                    }
                }
            }
            Ok(Value::Str(out))
        }
        Expr::Symbol(s) => Ok(Value::Symbol(s.clone())),
        Expr::Identifier(name) => {
            // Handle built-in constants
            if name == "None" {
                return Ok(Value::Enum {
                    enum_name: "Option".into(),
                    variant: "None".into(),
                    payload: None,
                });
            }
            env.get(name)
                .cloned()
                .ok_or_else(|| CompileError::Semantic(format!("undefined variable: {name}")))
        },
        Expr::New { kind, expr } => {
            if *kind != PointerKind::Unique {
                return Err(CompileError::Semantic("only unique (&) allocation is supported right now".into()));
            }
            let inner = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            Ok(Value::Unique(ManualUniqueValue::new(inner)))
        }
        Expr::Binary { op, left, right } => {
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
            match op {
                BinOp::Add => match (left_val, right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
                    (Value::Str(a), b) => Ok(Value::Str(format!("{a}{}", b.to_display_string()))),
                    (a, Value::Str(b)) => Ok(Value::Str(format!("{}{}", a.to_display_string(), b))),
                    (l, r) => Ok(Value::Int(l.as_int()? + r.as_int()?)),
                },
                BinOp::Sub => Ok(Value::Int(left_val.as_int()? - right_val.as_int()?)),
                BinOp::Mul => Ok(Value::Int(left_val.as_int()? * right_val.as_int()?)),
                BinOp::Div => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("division by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? / r))
                    }
                }
                BinOp::Mod => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("modulo by zero".into()))
                    } else {
                        Ok(Value::Int(left_val.as_int()? % r))
                    }
                }
                BinOp::Eq => Ok(Value::Bool(left_val == right_val)),
                BinOp::NotEq => Ok(Value::Bool(left_val != right_val)),
                BinOp::Lt => Ok(Value::Bool(left_val.as_int()? < right_val.as_int()?)),
                BinOp::Gt => Ok(Value::Bool(left_val.as_int()? > right_val.as_int()?)),
                BinOp::LtEq => Ok(Value::Bool(left_val.as_int()? <= right_val.as_int()?)),
                BinOp::GtEq => Ok(Value::Bool(left_val.as_int()? >= right_val.as_int()?)),
                BinOp::Is => Ok(Value::Bool(left_val == right_val)),
                BinOp::And => Ok(Value::Bool(left_val.truthy() && right_val.truthy())),
                BinOp::Or => Ok(Value::Bool(left_val.truthy() || right_val.truthy())),
                _ => Err(CompileError::Semantic(format!(
                    "unsupported binary operator: {:?}",
                    op
                ))),
            }
        }
        Expr::Unary { op, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)?;
            match op {
                UnaryOp::Neg => Ok(Value::Int(-val.as_int()?)),
                UnaryOp::Not => Ok(Value::Bool(!val.truthy())),
                _ => Err(CompileError::Semantic("unsupported unary op".into())),
            }
        }
        Expr::Lambda { params, body } => {
            let names: Vec<String> = params.iter().map(|LambdaParam { name, .. }| name.clone()).collect();
            Ok(Value::Lambda { params: names, body: body.clone(), env: env.clone() })
        }
        Expr::If { condition, then_branch, else_branch } => {
            if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)
            } else {
                Ok(Value::Nil)
            }
        }
        Expr::Call { callee, args } => {
            if let Expr::Identifier(name) = callee.as_ref() {
                match name.as_str() {
                    "range" => {
                        let start = args.get(0).map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)).transpose()?.unwrap_or(Value::Int(0)).as_int()?;
                        let end = args.get(1).map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)).transpose()?.unwrap_or(Value::Int(0)).as_int()?;
                        let inclusive = args.get(2).map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods)).transpose()?.unwrap_or(Value::Bool(false)).truthy();
                        let mut fields = HashMap::new();
                        fields.insert("start".into(), Value::Int(start));
                        fields.insert("end".into(), Value::Int(end));
                        fields.insert("inclusive".into(), Value::Bool(inclusive));
                        return Ok(Value::Object {
                            class: "__range__".into(),
                            fields,
                        });
                    }
                    "Some" => {
                        let val = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        return Ok(Value::Enum {
                            enum_name: "Option".into(),
                            variant: "Some".into(),
                            payload: Some(Box::new(val)),
                        });
                    }
                    "None" => {
                        return Ok(Value::Enum {
                            enum_name: "Option".into(),
                            variant: "None".into(),
                            payload: None,
                        });
                    }
                    "len" => {
                        let val = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        return match val {
                            Value::Array(a) => Ok(Value::Int(a.len() as i64)),
                            Value::Tuple(t) => Ok(Value::Int(t.len() as i64)),
                            Value::Dict(d) => Ok(Value::Int(d.len() as i64)),
                            Value::Str(s) => Ok(Value::Int(s.len() as i64)),
                            _ => Err(CompileError::Semantic("len expects array, tuple, dict, or string".into())),
                        };
                    }
                    "send" => {
                        let target = args.get(0).ok_or_else(|| CompileError::Semantic("send expects actor handle".into()))?;
                        let msg_arg = args.get(1).ok_or_else(|| CompileError::Semantic("send expects message".into()))?;
                        let target_val = evaluate_expr(&target.value, env, functions, classes, enums, impl_methods)?;
                        let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
                        if let Value::Actor(handle) = target_val {
                            handle
                                .send(Message::Value(msg_val.to_display_string()))
                                .map_err(|e| CompileError::Semantic(e))?;
                            return Ok(Value::Nil);
                        }
                        return Err(CompileError::Semantic("send target must be actor".into()));
                    }
                    "recv" => {
                        if !args.is_empty() {
                            return Err(CompileError::Semantic("recv takes no arguments".into()));
                        }
                        let msg = ACTOR_INBOX.with(|cell| {
                            cell.borrow()
                                .as_ref()
                                .ok_or_else(|| CompileError::Semantic("recv called outside actor".into()))
                                .and_then(|rx| {
                                    rx.lock()
                                        .map_err(|_| CompileError::Semantic("actor inbox lock poisoned".into()))
                                        .and_then(|receiver| {
                                            receiver
                                                .recv()
                                                .map_err(|e| CompileError::Semantic(format!("recv failed: {e}")))
                                        })
                                })
                        })?;
                        return Ok(match msg {
                            Message::Value(s) => Value::Str(s),
                            Message::Bytes(b) => Value::Str(String::from_utf8_lossy(&b).to_string()),
                        });
                    }
                    "reply" => {
                        let msg_arg = args.get(0).ok_or_else(|| CompileError::Semantic("reply expects message".into()))?;
                        let msg_val = evaluate_expr(&msg_arg.value, env, functions, classes, enums, impl_methods)?;
                        ACTOR_OUTBOX.with(|cell| {
                            cell.borrow()
                                .as_ref()
                                .ok_or_else(|| CompileError::Semantic("reply called outside actor".into()))
                                .and_then(|tx| {
                                    tx.send(Message::Value(msg_val.to_display_string()))
                                        .map_err(|e| CompileError::Semantic(format!("reply failed: {e}")))
                                })
                        })?;
                        return Ok(Value::Nil);
                    }
                    "join" => {
                        let handle_arg = args.get(0).ok_or_else(|| CompileError::Semantic("join expects actor handle".into()))?;
                        let handle_val = evaluate_expr(&handle_arg.value, env, functions, classes, enums, impl_methods)?;
                        if let Value::Actor(handle) = handle_val {
                            handle.join().map_err(|e| CompileError::Semantic(e))?;
                            return Ok(Value::Nil);
                        }
                        return Err(CompileError::Semantic("join target must be actor".into()));
                    }
                    "spawn" => {
                        // Spawn a new actor evaluating the first argument expression.
                        let inner_expr = args.get(0).ok_or_else(|| CompileError::Semantic("spawn expects a thunk".into()))?;
                        let expr_clone = inner_expr.value.clone();
                        let env_clone = env.clone();
                        let funcs = functions.clone();
                        let classes_clone = classes.clone();
                        let enums_clone = enums.clone();
                        let impls_clone = impl_methods.clone();
                        let handle = concurrency::spawn_actor(move |inbox, outbox| {
                            let inbox = Arc::new(Mutex::new(inbox));
                            ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
                            ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));
                            let _ = evaluate_expr(&expr_clone, &env_clone, &funcs, &classes_clone, &enums_clone, &impls_clone);
                            ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
                            ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
                        });
                        return Ok(Value::Actor(handle));
                    }
                    _ => {
                        if let Some(func) = functions.get(name) {
                            return exec_function(func, args, env, functions, classes, enums, impl_methods, None);
                        }
                        // Check for extern functions
                        let is_extern = EXTERN_FUNCTIONS.with(|cell| cell.borrow().contains(name));
                        if is_extern {
                            return call_extern_function(name, args, env, functions, classes, enums, impl_methods);
                        }
                        // Check for context block - dispatch to context object as method call
                        let context_obj = CONTEXT_OBJECT.with(|cell| cell.borrow().clone());
                        if let Some(ctx) = context_obj {
                            return dispatch_context_method(&ctx, name, args, env, functions, classes, enums, impl_methods);
                        }
                    }
                }
            }
            if let Expr::Path(segments) = callee.as_ref() {
                // Handle enum variant constructor: EnumName::Variant(payload)
                if segments.len() == 2 {
                    let enum_name = &segments[0];
                    let variant = &segments[1];
                    if let Some(variants) = enums.get(enum_name) {
                        if variants.contains(variant) {
                            // Evaluate the first argument as the payload
                            let payload = if !args.is_empty() {
                                Some(Box::new(evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?))
                            } else {
                                None
                            };
                            return Ok(Value::Enum {
                                enum_name: enum_name.clone(),
                                variant: variant.clone(),
                                payload,
                            });
                        }
                    }
                }
                return Err(CompileError::Semantic(format!("unsupported path call: {:?}", segments)));
            }

            let callee_val = evaluate_expr(callee, env, functions, classes, enums, impl_methods)?;
            match callee_val {
                Value::Lambda { params, body, env: captured } => {
                    exec_lambda(&params, &body, args, env, &captured, functions, classes, enums, impl_methods)
                }
                _ => Err(CompileError::Semantic("unsupported callee".into())),
            }
        }
        Expr::MethodCall { receiver, method, args } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_unique();
            // Built-in methods for Array
            if let Value::Array(ref arr) = recv_val {
                match method.as_str() {
                    "len" => return Ok(Value::Int(arr.len() as i64)),
                    "is_empty" => return Ok(Value::Bool(arr.is_empty())),
                    "first" => return Ok(arr.first().cloned().unwrap_or(Value::Nil)),
                    "last" => return Ok(arr.last().cloned().unwrap_or(Value::Nil)),
                    "get" => {
                        let idx = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0))
                            .as_int()? as usize;
                        return Ok(arr.get(idx).cloned().unwrap_or(Value::Nil));
                    }
                    "contains" => {
                        let needle = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        return Ok(Value::Bool(arr.contains(&needle)));
                    }
                    // Functional methods that return new arrays
                    "push" | "append" => {
                        let item = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        let mut new_arr = arr.clone();
                        new_arr.push(item);
                        return Ok(Value::Array(new_arr));
                    }
                    "pop" => {
                        let mut new_arr = arr.clone();
                        new_arr.pop();
                        return Ok(Value::Array(new_arr));
                    }
                    "concat" | "extend" => {
                        let other = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Array(vec![]));
                        if let Value::Array(other_arr) = other {
                            let mut new_arr = arr.clone();
                            new_arr.extend(other_arr);
                            return Ok(Value::Array(new_arr));
                        }
                        return Err(CompileError::Semantic("concat expects array argument".into()));
                    }
                    "insert" => {
                        let idx = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0))
                            .as_int()? as usize;
                        let item = args.get(1)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        let mut new_arr = arr.clone();
                        if idx <= new_arr.len() {
                            new_arr.insert(idx, item);
                        }
                        return Ok(Value::Array(new_arr));
                    }
                    "remove" => {
                        let idx = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0))
                            .as_int()? as usize;
                        let mut new_arr = arr.clone();
                        if idx < new_arr.len() {
                            new_arr.remove(idx);
                        }
                        return Ok(Value::Array(new_arr));
                    }
                    "reverse" => {
                        let mut new_arr = arr.clone();
                        new_arr.reverse();
                        return Ok(Value::Array(new_arr));
                    }
                    "slice" => {
                        let start = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0))
                            .as_int()? as usize;
                        let end = args.get(1)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .map(|v| v.as_int().unwrap_or(arr.len() as i64) as usize)
                            .unwrap_or(arr.len());
                        let end = end.min(arr.len());
                        let start = start.min(end);
                        return Ok(Value::Array(arr[start..end].to_vec()));
                    }
                    "map" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            let mut result = Vec::new();
                            for item in arr {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), item.clone());
                                }
                                result.push(evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?);
                            }
                            return Ok(Value::Array(result));
                        }
                        return Err(CompileError::Semantic("map expects lambda argument".into()));
                    }
                    "filter" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            let mut result = Vec::new();
                            for item in arr {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), item.clone());
                                }
                                let keep = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                if keep.truthy() {
                                    result.push(item.clone());
                                }
                            }
                            return Ok(Value::Array(result));
                        }
                        return Err(CompileError::Semantic("filter expects lambda argument".into()));
                    }
                    "reduce" | "fold" => {
                        let init = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0));
                        let func = args.get(1)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            let mut acc = init;
                            for item in arr {
                                let mut local_env = captured.clone();
                                if params.len() >= 2 {
                                    local_env.insert(params[0].clone(), acc.clone());
                                    local_env.insert(params[1].clone(), item.clone());
                                }
                                acc = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                            }
                            return Ok(acc);
                        }
                        return Err(CompileError::Semantic("reduce expects lambda argument".into()));
                    }
                    "find" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            for item in arr {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), item.clone());
                                }
                                let matches = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                if matches.truthy() {
                                    return Ok(Value::Enum {
                                        enum_name: "Option".into(),
                                        variant: "Some".into(),
                                        payload: Some(Box::new(item.clone())),
                                    });
                                }
                            }
                            return Ok(Value::Enum {
                                enum_name: "Option".into(),
                                variant: "None".into(),
                                payload: None,
                            });
                        }
                        return Err(CompileError::Semantic("find expects lambda argument".into()));
                    }
                    "any" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            for item in arr {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), item.clone());
                                }
                                let matches = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                if matches.truthy() {
                                    return Ok(Value::Bool(true));
                                }
                            }
                            return Ok(Value::Bool(false));
                        }
                        return Err(CompileError::Semantic("any expects lambda argument".into()));
                    }
                    "all" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            for item in arr {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), item.clone());
                                }
                                let matches = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                if !matches.truthy() {
                                    return Ok(Value::Bool(false));
                                }
                            }
                            return Ok(Value::Bool(true));
                        }
                        return Err(CompileError::Semantic("all expects lambda argument".into()));
                    }
                    "join" => {
                        let sep = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Str("".into()))
                            .to_display_string();
                        let parts: Vec<String> = arr.iter().map(|v| v.to_display_string()).collect();
                        return Ok(Value::Str(parts.join(&sep)));
                    }
                    "sum" => {
                        let mut total: i64 = 0;
                        for item in arr {
                            if let Value::Int(n) = item {
                                total += n;
                            }
                        }
                        return Ok(Value::Int(total));
                    }
                    "index_of" => {
                        let needle = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        for (i, item) in arr.iter().enumerate() {
                            if item == &needle {
                                return Ok(Value::Int(i as i64));
                            }
                        }
                        return Ok(Value::Int(-1));
                    }
                    _ => {}
                }
            }
            // Built-in methods for Tuple
            if let Value::Tuple(ref tup) = recv_val {
                match method.as_str() {
                    "len" => return Ok(Value::Int(tup.len() as i64)),
                    "get" => {
                        let idx = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Int(0))
                            .as_int()? as usize;
                        return Ok(tup.get(idx).cloned().unwrap_or(Value::Nil));
                    }
                    _ => {}
                }
            }
            // Built-in methods for Dict
            if let Value::Dict(ref map) = recv_val {
                match method.as_str() {
                    "len" => return Ok(Value::Int(map.len() as i64)),
                    "is_empty" => return Ok(Value::Bool(map.is_empty())),
                    "contains_key" => {
                        let key = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil)
                            .to_key_string();
                        return Ok(Value::Bool(map.contains_key(&key)));
                    }
                    "get" => {
                        let key = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil)
                            .to_key_string();
                        return Ok(map.get(&key).cloned().unwrap_or(Value::Nil));
                    }
                    "keys" => {
                        let keys: Vec<Value> = map.keys().map(|k| Value::Str(k.clone())).collect();
                        return Ok(Value::Array(keys));
                    }
                    "values" => {
                        let vals: Vec<Value> = map.values().cloned().collect();
                        return Ok(Value::Array(vals));
                    }
                    // Functional methods that return new dicts
                    "set" | "insert" => {
                        let key = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil)
                            .to_key_string();
                        let value = args.get(1)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        let mut new_map = map.clone();
                        new_map.insert(key, value);
                        return Ok(Value::Dict(new_map));
                    }
                    "remove" | "delete" => {
                        let key = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil)
                            .to_key_string();
                        let mut new_map = map.clone();
                        new_map.remove(&key);
                        return Ok(Value::Dict(new_map));
                    }
                    "merge" | "extend" => {
                        let other = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Dict(HashMap::new()));
                        if let Value::Dict(other_map) = other {
                            let mut new_map = map.clone();
                            new_map.extend(other_map);
                            return Ok(Value::Dict(new_map));
                        }
                        return Err(CompileError::Semantic("merge expects dict argument".into()));
                    }
                    "get_or" => {
                        let key = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil)
                            .to_key_string();
                        let default = args.get(1)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        return Ok(map.get(&key).cloned().unwrap_or(default));
                    }
                    "entries" | "items" => {
                        let entries: Vec<Value> = map.iter()
                            .map(|(k, v)| Value::Tuple(vec![Value::Str(k.clone()), v.clone()]))
                            .collect();
                        return Ok(Value::Array(entries));
                    }
                    "map_values" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            let mut new_map = HashMap::new();
                            for (k, v) in map {
                                let mut local_env = captured.clone();
                                if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), v.clone());
                                }
                                let new_val = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                new_map.insert(k.clone(), new_val);
                            }
                            return Ok(Value::Dict(new_map));
                        }
                        return Err(CompileError::Semantic("map_values expects lambda argument".into()));
                    }
                    "filter" => {
                        let func = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Nil);
                        if let Value::Lambda { params, body, env: captured } = func {
                            let mut new_map = HashMap::new();
                            for (k, v) in map {
                                let mut local_env = captured.clone();
                                if params.len() >= 2 {
                                    local_env.insert(params[0].clone(), Value::Str(k.clone()));
                                    local_env.insert(params[1].clone(), v.clone());
                                } else if let Some(param) = params.first() {
                                    local_env.insert(param.clone(), v.clone());
                                }
                                let keep = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                if keep.truthy() {
                                    new_map.insert(k.clone(), v.clone());
                                }
                            }
                            return Ok(Value::Dict(new_map));
                        }
                        return Err(CompileError::Semantic("filter expects lambda argument".into()));
                    }
                    _ => {}
                }
            }
            // Built-in methods for String
            if let Value::Str(ref s) = recv_val {
                match method.as_str() {
                    "len" => return Ok(Value::Int(s.len() as i64)),
                    "is_empty" => return Ok(Value::Bool(s.is_empty())),
                    "chars" => {
                        let chars: Vec<Value> = s.chars().map(|c| Value::Str(c.to_string())).collect();
                        return Ok(Value::Array(chars));
                    }
                    "contains" => {
                        let needle = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Str(String::new()))
                            .to_key_string();
                        return Ok(Value::Bool(s.contains(&needle)));
                    }
                    "starts_with" => {
                        let prefix = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Str(String::new()))
                            .to_key_string();
                        return Ok(Value::Bool(s.starts_with(&prefix)));
                    }
                    "ends_with" => {
                        let suffix = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Str(String::new()))
                            .to_key_string();
                        return Ok(Value::Bool(s.ends_with(&suffix)));
                    }
                    "to_upper" => return Ok(Value::Str(s.to_uppercase())),
                    "to_lower" => return Ok(Value::Str(s.to_lowercase())),
                    "trim" => return Ok(Value::Str(s.trim().to_string())),
                    "split" => {
                        let sep = args.get(0)
                            .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                            .transpose()?
                            .unwrap_or(Value::Str(" ".into()))
                            .to_key_string();
                        let parts: Vec<Value> = s.split(&sep).map(|p| Value::Str(p.to_string())).collect();
                        return Ok(Value::Array(parts));
                    }
                    _ => {}
                }
            }
            // Built-in methods for Option (Enum with enum_name == "Option")
            if let Value::Enum { enum_name, variant, payload } = &recv_val {
                if enum_name == "Option" {
                    match method.as_str() {
                        "is_some" => return Ok(Value::Bool(variant == "Some")),
                        "is_none" => return Ok(Value::Bool(variant == "None")),
                        "unwrap" => {
                            if variant == "Some" {
                                if let Some(val) = payload {
                                    return Ok(val.as_ref().clone());
                                }
                            }
                            return Err(CompileError::Semantic("called unwrap on None".into()));
                        }
                        "unwrap_or" => {
                            if variant == "Some" {
                                if let Some(val) = payload {
                                    return Ok(val.as_ref().clone());
                                }
                            }
                            let default = args.get(0)
                                .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                                .transpose()?
                                .unwrap_or(Value::Nil);
                            return Ok(default);
                        }
                        "map" => {
                            if variant == "Some" {
                                if let Some(val) = payload {
                                    let func_arg = args.get(0)
                                        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
                                        .transpose()?
                                        .unwrap_or(Value::Nil);
                                    if let Value::Lambda { params, body, env: captured } = func_arg {
                                        let mut local_env = captured.clone();
                                        if let Some(param) = params.first() {
                                            local_env.insert(param.clone(), val.as_ref().clone());
                                        }
                                        let result = evaluate_expr(&body, &local_env, functions, classes, enums, impl_methods)?;
                                        return Ok(Value::Enum {
                                            enum_name: "Option".into(),
                                            variant: "Some".into(),
                                            payload: Some(Box::new(result)),
                                        });
                                    }
                                }
                            }
                            return Ok(Value::Enum {
                                enum_name: "Option".into(),
                                variant: "None".into(),
                                payload: None,
                            });
                        }
                        _ => {}
                    }
                }
            }
            // Object methods (class/struct)
            if let Value::Object { class, fields } = recv_val.clone() {
                // First check class methods
                if let Some(class_def) = classes.get(&class) {
                    if let Some(func) = class_def.methods.iter().find(|m| &m.name == method) {
                        return exec_function(
                            func,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((&class, &fields)),
                        );
                    }
                }
                // Then check impl block methods
                if let Some(methods) = impl_methods.get(&class) {
                    if let Some(func) = methods.iter().find(|m| &m.name == method) {
                        return exec_function(
                            func,
                            args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((&class, &fields)),
                        );
                    }
                }
                // Check for method_missing hook
                if let Some(class_def) = classes.get(&class) {
                    if let Some(mm_func) = class_def.methods.iter().find(|m| m.name == "method_missing") {
                        // Call method_missing with (name: Symbol, args: Array, block: Nil)
                        let mm_args = vec![
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Symbol(method.clone()),
                            },
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
                            },
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Nil,
                            },
                        ];
                        return exec_function(
                            mm_func,
                            &mm_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((&class, &fields)),
                        );
                    }
                }
                // Also check impl blocks for method_missing
                if let Some(methods) = impl_methods.get(&class) {
                    if let Some(mm_func) = methods.iter().find(|m| m.name == "method_missing") {
                        let mm_args = vec![
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Symbol(method.clone()),
                            },
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
                            },
                            simple_parser::ast::Argument {
                                name: None,
                                value: Expr::Nil,
                            },
                        ];
                        return exec_function(
                            mm_func,
                            &mm_args,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                            Some((&class, &fields)),
                        );
                    }
                }
                return Err(CompileError::Semantic(format!("unknown method {method} on {class}")));
            }
            Err(CompileError::Semantic(format!("method call on unsupported type: {method}")))
        }
        Expr::FieldAccess { receiver, field } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_unique();
            if let Value::Object { fields, .. } = recv_val {
                fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| CompileError::Semantic(format!("unknown field {field}")))
            } else {
                Err(CompileError::Semantic("field access on non-object".into()))
            }
        }
        Expr::StructInit { name, fields } => {
            let mut map = HashMap::new();
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
            Ok(Value::Object {
                class: name.clone(),
                fields: map,
            })
        }
        Expr::Path(segments) => {
            // Handle enum variant access: EnumName::Variant
            if segments.len() == 2 {
                let enum_name = &segments[0];
                let variant = &segments[1];
                if let Some(variants) = enums.get(enum_name) {
                    if variants.contains(variant) {
                        Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: variant.clone(),
                            payload: None,
                        })
                    } else {
                        Err(CompileError::Semantic(format!(
                            "unknown variant {variant} for enum {enum_name}"
                        )))
                    }
                } else {
                    Err(CompileError::Semantic(format!("unknown enum: {enum_name}")))
                }
            } else {
                Err(CompileError::Semantic(format!(
                    "unsupported path: {:?}",
                    segments
                )))
            }
        }
        Expr::Dict(entries) => {
            let mut map = HashMap::new();
            for (k, v) in entries {
                let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                map.insert(key_val.to_key_string(), val);
            }
            Ok(Value::Dict(map))
        }
        Expr::Range { start, end, inclusive } => {
            let start = start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            let end = end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            let mut fields = HashMap::new();
            fields.insert("start".into(), Value::Int(start));
            fields.insert("end".into(), Value::Int(end));
            fields.insert("inclusive".into(), Value::Bool(*inclusive));
            Ok(Value::Object {
                class: "__range__".into(),
                fields,
            })
        }
        Expr::Array(items) => {
            let mut arr = Vec::new();
            for item in items {
                arr.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Array(arr))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(item, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Tuple(tup))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?.deref_unique();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
            match recv_val {
                Value::Array(arr) => {
                    let idx = idx_val.as_int()? as usize;
                    arr.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("array index out of bounds: {idx}")))
                }
                Value::Tuple(tup) => {
                    let idx = idx_val.as_int()? as usize;
                    tup.get(idx)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("tuple index out of bounds: {idx}")))
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    map.get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
                }
                Value::Str(s) => {
                    let idx = idx_val.as_int()? as usize;
                    s.chars()
                        .nth(idx)
                        .map(|c| Value::Str(c.to_string()))
                        .ok_or_else(|| CompileError::Semantic(format!("string index out of bounds: {idx}")))
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic("index access on non-indexable type".into())),
            }
        }
        Expr::Spawn(inner) => {
            let env_clone = env.clone();
            let funcs = functions.clone();
            let classes_clone = classes.clone();
            let enums_clone = enums.clone();
            let impls_clone = impl_methods.clone();
            let inner_expr = (*inner).clone();
            let handle = concurrency::spawn_actor(move |inbox, outbox| {
                let inbox = Arc::new(Mutex::new(inbox));
                ACTOR_INBOX.with(|cell| *cell.borrow_mut() = Some(inbox.clone()));
                ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = Some(outbox.clone()));
                let _ = evaluate_expr(&inner_expr, &env_clone, &funcs, &classes_clone, &enums_clone, &impls_clone);
                ACTOR_INBOX.with(|cell| *cell.borrow_mut() = None);
                ACTOR_OUTBOX.with(|cell| *cell.borrow_mut() = None);
            });
            Ok(Value::Actor(handle))
        }
        Expr::FunctionalUpdate { target, method, args } => {
            // When used as an expression (not statement), just evaluate as method call
            // The assignment semantics are handled at the statement level
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
        }
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}

fn bind_args(
    params: &[simple_parser::ast::Parameter],
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    skip_self: bool,
) -> Result<HashMap<String, Value>, CompileError> {
    let params_to_bind: Vec<_> = params
        .iter()
        .filter(|p| !(skip_self && p.name == "self"))
        .collect();

    let mut bound = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let val = evaluate_expr(&arg.value, outer_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            if !params_to_bind.iter().any(|p| &p.name == name) {
                return Err(CompileError::Semantic(format!("unknown argument {name}")));
            }
            bound.insert(name.clone(), val);
        } else {
            if positional_idx >= params_to_bind.len() {
                return Err(CompileError::Semantic("too many arguments".into()));
            }
            let param = params_to_bind[positional_idx];
            bound.insert(param.name.clone(), val);
            positional_idx += 1;
        }
    }

    for param in params_to_bind {
        if !bound.contains_key(&param.name) {
            if let Some(default_expr) = &param.default {
                let v = evaluate_expr(default_expr, outer_env, functions, classes, enums, impl_methods)?;
                bound.insert(param.name.clone(), v);
            } else {
                return Err(CompileError::Semantic(format!("missing argument {}", param.name)));
            }
        }
    }

    Ok(bound)
}

fn exec_lambda(
    params: &[String],
    body: &Expr,
    args: &[simple_parser::ast::Argument],
    call_env: &Env,
    captured_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut local_env = captured_env.clone();
    let mut positional_idx = 0usize;

    for arg in args {
        let val = evaluate_expr(&arg.value, call_env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            local_env.insert(name.clone(), val);
        } else {
            if positional_idx >= params.len() {
                return Err(CompileError::Semantic("too many arguments to lambda".into()));
            }
            local_env.insert(params[positional_idx].clone(), val);
            positional_idx += 1;
        }
    }

    for param in params {
        if !local_env.contains_key(param) {
            local_env.insert(param.clone(), Value::Nil);
        }
    }

    evaluate_expr(body, &local_env, functions, classes, enums, impl_methods)
}

fn exec_function(
    func: &FunctionDef,
    args: &[simple_parser::ast::Argument],
    outer_env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
    self_ctx: Option<(&str, &HashMap<String, Value>)>,
) -> Result<Value, CompileError> {
    let mut local_env = Env::new();
    if let Some((class_name, fields)) = self_ctx {
        local_env.insert(
            "self".into(),
            Value::Object {
                class: class_name.to_string(),
                fields: fields.clone(),
            },
        );
    }
    let bound = bind_args(
        &func.params,
        args,
        outer_env,
        functions,
        classes,
        enums,
        impl_methods,
        self_ctx.is_some(),
    )?;
    for (name, val) in bound {
        local_env.insert(name, val);
    }
    match exec_block(&func.body, &mut local_env, functions, classes, enums, impl_methods)? {
        Control::Return(v) => Ok(v),
        _ => Ok(Value::Nil),
    }
}

/// Call an extern function with built-in implementation
fn call_extern_function(
    name: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Evaluate all arguments first
    let evaluated: Vec<Value> = args
        .iter()
        .map(|a| evaluate_expr(&a.value, env, functions, classes, enums, impl_methods))
        .collect::<Result<Vec<_>, _>>()?;

    match name {
        // I/O functions
        "print" => {
            for val in &evaluated {
                print!("{}", val.to_display_string());
            }
            Ok(Value::Nil)
        }
        "println" => {
            for val in &evaluated {
                print!("{}", val.to_display_string());
            }
            println!();
            Ok(Value::Nil)
        }
        "input" => {
            use std::io::{self, BufRead};
            let stdin = io::stdin();
            let line = stdin.lock().lines().next()
                .transpose()
                .map_err(|e| CompileError::Semantic(format!("input error: {e}")))?
                .unwrap_or_default();
            Ok(Value::Str(line))
        }

        // Math functions
        "abs" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("abs expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(i.abs())),
                _ => Err(CompileError::Semantic("abs expects integer".into())),
            }
        }
        "min" => {
            let a = evaluated.get(0).ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?.as_int()?;
            let b = evaluated.get(1).ok_or_else(|| CompileError::Semantic("min expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(a.min(b)))
        }
        "max" => {
            let a = evaluated.get(0).ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?.as_int()?;
            let b = evaluated.get(1).ok_or_else(|| CompileError::Semantic("max expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(a.max(b)))
        }
        "sqrt" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("sqrt expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int((val as f64).sqrt() as i64))
        }
        "floor" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("floor expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int(val))  // Integer floor is identity
        }
        "ceil" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("ceil expects 1 argument".into()))?.as_int()?;
            Ok(Value::Int(val))  // Integer ceil is identity
        }
        "pow" => {
            let base = evaluated.get(0).ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?.as_int()?;
            let exp = evaluated.get(1).ok_or_else(|| CompileError::Semantic("pow expects 2 arguments".into()))?.as_int()?;
            Ok(Value::Int(base.pow(exp as u32)))
        }

        // Conversion functions
        "to_string" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("to_string expects 1 argument".into()))?;
            Ok(Value::Str(val.to_display_string()))
        }
        "to_int" => {
            let val = evaluated.first().ok_or_else(|| CompileError::Semantic("to_int expects 1 argument".into()))?;
            match val {
                Value::Int(i) => Ok(Value::Int(*i)),
                Value::Str(s) => s.parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| CompileError::Semantic(format!("cannot convert '{}' to int", s))),
                Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
                _ => Err(CompileError::Semantic("to_int expects string, int, or bool".into())),
            }
        }

        // Process control
        "exit" => {
            let code = evaluated.first()
                .map(|v| v.as_int())
                .transpose()?
                .unwrap_or(0) as i32;
            std::process::exit(code);
        }

        // Unknown extern function
        _ => Err(CompileError::Semantic(format!("unknown extern function: {}", name))),
    }
}

/// Dispatch a method call to the context object
fn dispatch_context_method(
    ctx: &Value,
    method: &str,
    args: &[simple_parser::ast::Argument],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // For objects with class, look up the method in class or impl blocks
    if let Value::Object { class, fields } = ctx {
        // Check for class methods
        if let Some(class_def) = classes.get(class) {
            for method_def in &class_def.methods {
                if method_def.name == method {
                    return exec_function(method_def, args, env, functions, classes, enums, impl_methods, Some((class, fields)));
                }
            }
        }
        // Check impl methods
        if let Some(methods) = impl_methods.get(class) {
            for method_def in methods {
                if method_def.name == method {
                    return exec_function(method_def, args, env, functions, classes, enums, impl_methods, Some((class, fields)));
                }
            }
        }
        // Check for method_missing hook
        if let Some(class_def) = classes.get(class) {
            if let Some(mm_func) = class_def.methods.iter().find(|m| m.name == "method_missing") {
                let mm_args = vec![
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Symbol(method.to_string()),
                    },
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
                    },
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Nil,
                    },
                ];
                return exec_function(mm_func, &mm_args, env, functions, classes, enums, impl_methods, Some((class, fields)));
            }
        }
        // Also check impl blocks for method_missing
        if let Some(methods) = impl_methods.get(class) {
            if let Some(mm_func) = methods.iter().find(|m| m.name == "method_missing") {
                let mm_args = vec![
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Symbol(method.to_string()),
                    },
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Array(args.iter().map(|a| a.value.clone()).collect()),
                    },
                    simple_parser::ast::Argument {
                        name: None,
                        value: Expr::Nil,
                    },
                ];
                return exec_function(mm_func, &mm_args, env, functions, classes, enums, impl_methods, Some((class, fields)));
            }
        }
        return Err(CompileError::Semantic(format!("context object has no method '{}'", method)));
    }

    // For arrays, dicts, etc. - delegate to the standard method handling
    // by creating a method call expression and evaluating it
    let recv_expr = value_to_expr(ctx)?;
    let method_call = Expr::MethodCall {
        receiver: Box::new(recv_expr),
        method: method.to_string(),
        args: args.to_vec(),
    };
    evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
}

/// Convert a Value back to an Expr for evaluation purposes
fn value_to_expr(val: &Value) -> Result<Expr, CompileError> {
    Ok(match val {
        Value::Int(i) => Expr::Integer(*i),
        Value::Bool(b) => Expr::Bool(*b),
        Value::Str(s) => Expr::String(s.clone()),
        Value::Symbol(s) => Expr::Symbol(s.clone()),
        Value::Nil => Expr::Nil,
        Value::Array(items) => {
            let exprs: Result<Vec<_>, _> = items.iter().map(value_to_expr).collect();
            Expr::Array(exprs?)
        }
        Value::Tuple(items) => {
            let exprs: Result<Vec<_>, _> = items.iter().map(value_to_expr).collect();
            Expr::Tuple(exprs?)
        }
        _ => return Err(CompileError::Semantic("cannot convert value to expression".into())),
    })
}
