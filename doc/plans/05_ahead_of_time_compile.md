# Ahead-of-Time Compilation Plan

## Overview

Implement AOT compilation for Simple language that compiles source to native code (.smf files) before execution. This enables interpreter-like workflow: edit -> run (compile happens automatically if source changed).

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     AOT Compilation Pipeline                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐       │
│  │  Source  │───▶│  Parser  │───▶│   HIR    │───▶│   MIR    │       │
│  │  .simple │    │  (AST)   │    │(High IR) │    │ (Mid IR) │       │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘       │
│                                                        │             │
│                                                        ▼             │
│                                         ┌──────────────────────┐    │
│                                         │    Code Generator    │    │
│                                         │  ┌────────────────┐  │    │
│                                         │  │   Cranelift    │  │    │
│                                         │  │   (or LLVM)    │  │    │
│                                         │  └────────────────┘  │    │
│                                         └──────────┬───────────┘    │
│                                                    │                 │
│                                                    ▼                 │
│  ┌──────────┐    ┌──────────┐    ┌──────────────────────────┐       │
│  │  Output  │◀───│  Linker  │◀───│    Native Code (.o)      │       │
│  │   .smf   │    │  (SMF)   │    │                          │       │
│  └──────────┘    └──────────┘    └──────────────────────────┘       │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/compiler/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── pipeline.rs         # Main compilation pipeline
    ├── hir/
    │   ├── mod.rs          # High-level IR
    │   ├── lower.rs        # AST -> HIR
    │   └── types.rs        # HIR types
    ├── mir/
    │   ├── mod.rs          # Mid-level IR
    │   ├── lower.rs        # HIR -> MIR
    │   ├── optimize.rs     # MIR optimizations
    │   └── types.rs        # MIR types
    ├── codegen/
    │   ├── mod.rs          # Code generation
    │   ├── cranelift.rs    # Cranelift backend
    │   └── abi.rs          # Calling conventions
    ├── linker/
    │   ├── mod.rs          # SMF linker
    │   └── emit.rs         # SMF file emission
    └── cache/
        ├── mod.rs          # Compilation cache
        └── incremental.rs  # Incremental compilation
```

---

## High-Level IR (HIR)

### HIR Types (hir/types.rs)

```rust
// crates/compiler/src/hir/types.rs

use std::collections::HashMap;

/// Module after type checking
#[derive(Debug)]
pub struct HirModule {
    pub name: String,
    pub source_hash: u64,
    pub items: Vec<HirItem>,
    pub types: TypeTable,
}

#[derive(Debug)]
pub enum HirItem {
    Function(HirFunction),
    Struct(HirStruct),
    Enum(HirEnum),
    Trait(HirTrait),
    Impl(HirImpl),
    Actor(HirActor),
    Constant(HirConstant),
}

#[derive(Debug)]
pub struct HirFunction {
    pub name: String,
    pub params: Vec<HirParam>,
    pub return_type: TypeId,
    pub body: HirBlock,
    pub is_public: bool,
    pub effect: Effect,
}

#[derive(Debug, Clone, Copy)]
pub enum Effect {
    None,
    Async,
    Async,
}

#[derive(Debug)]
pub struct HirParam {
    pub name: String,
    pub ty: TypeId,
    pub is_mutable: bool,
}

#[derive(Debug)]
pub struct HirBlock {
    pub stmts: Vec<HirStmt>,
    pub expr: Option<Box<HirExpr>>,
}

#[derive(Debug)]
pub enum HirStmt {
    Let {
        name: String,
        ty: TypeId,
        init: Option<HirExpr>,
        is_mutable: bool,
    },
    Assign {
        target: HirExpr,
        value: HirExpr,
    },
    Expr(HirExpr),
    Return(Option<HirExpr>),
    Break(Option<String>),
    Continue(Option<String>),
}

#[derive(Debug)]
pub enum HirExpr {
    // Literals (with resolved types)
    IntLit(i64, TypeId),
    FloatLit(f64, TypeId),
    BoolLit(bool),
    StringLit(String),
    NilLit,

    // References
    Var(String, TypeId),
    Field {
        base: Box<HirExpr>,
        field: String,
        ty: TypeId,
    },
    Index {
        base: Box<HirExpr>,
        index: Box<HirExpr>,
        ty: TypeId,
    },

    // Operations
    Binary {
        op: BinOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
        ty: TypeId,
    },
    Unary {
        op: UnaryOp,
        operand: Box<HirExpr>,
        ty: TypeId,
    },
    Call {
        func: Box<HirExpr>,
        args: Vec<HirExpr>,
        ty: TypeId,
    },
    MethodCall {
        receiver: Box<HirExpr>,
        method: String,
        args: Vec<HirExpr>,
        ty: TypeId,
    },

    // Control flow
    If {
        condition: Box<HirExpr>,
        then_branch: HirBlock,
        else_branch: Option<HirBlock>,
        ty: TypeId,
    },
    Match {
        subject: Box<HirExpr>,
        arms: Vec<HirMatchArm>,
        ty: TypeId,
    },
    Loop {
        label: Option<String>,
        body: HirBlock,
    },

    // Constructors
    Struct {
        name: String,
        fields: Vec<(String, HirExpr)>,
        ty: TypeId,
    },
    Tuple(Vec<HirExpr>, TypeId),
    Array(Vec<HirExpr>, TypeId),

    // Memory
    New {
        kind: PointerKind,
        ty: TypeId,
        args: Vec<HirExpr>,
    },
    Borrow {
        mutable: bool,
        expr: Box<HirExpr>,
        ty: TypeId,
    },
    Deref {
        expr: Box<HirExpr>,
        ty: TypeId,
    },

    // Concurrency
    Spawn {
        expr: Box<HirExpr>,
        ty: TypeId,
    },
    Send {
        target: Box<HirExpr>,
        message: Box<HirExpr>,
    },

    // Lambda
    Lambda {
        params: Vec<HirParam>,
        body: HirBlock,
        captures: Vec<String>,
        ty: TypeId,
    },

    // Type cast
    Cast {
        expr: Box<HirExpr>,
        target_ty: TypeId,
    },
}

/// Type ID for efficient type comparison
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// Type table for interned types
pub struct TypeTable {
    types: Vec<Type>,
    intern_map: HashMap<Type, TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    // Primitives
    Int,
    Float,
    Bool,
    Char,
    String,
    Nil,

    // Compound
    Tuple(Vec<TypeId>),
    Array(TypeId, Option<usize>),
    Function { params: Vec<TypeId>, ret: TypeId },

    // User-defined
    Struct(String),
    Enum(String),
    Trait(String),
    Actor(String),

    // Pointers
    Pointer(PointerKind, TypeId),
    Borrow { mutable: bool, inner: TypeId },

    // Type variable (for generics)
    TypeVar(u32),
}
```

### AST to HIR Lowering (hir/lower.rs)

```rust
// crates/compiler/src/hir/lower.rs

use crate::parser::ast::*;
use crate::hir::*;

pub struct HirLowering {
    types: TypeTable,
    current_function: Option<String>,
    scope_stack: Vec<Scope>,
}

struct Scope {
    variables: HashMap<String, (TypeId, bool)>,  // name -> (type, is_mutable)
}

impl HirLowering {
    pub fn new() -> Self {
        Self {
            types: TypeTable::new(),
            current_function: None,
            scope_stack: vec![Scope::new()],
        }
    }

    pub fn lower_module(&mut self, module: &Module) -> Result<HirModule, LowerError> {
        let mut items = Vec::new();

        for def in &module.definitions {
            match def {
                Node::Function(f) => {
                    items.push(HirItem::Function(self.lower_function(f)?));
                }
                Node::Struct(s) => {
                    items.push(HirItem::Struct(self.lower_struct(s)?));
                }
                // ... more definitions
                _ => {}
            }
        }

        Ok(HirModule {
            name: module.name.clone(),
            source_hash: hash_source(&module.source),
            items,
            types: std::mem::take(&mut self.types),
        })
    }

    fn lower_function(&mut self, func: &FunctionDef) -> Result<HirFunction, LowerError> {
        self.push_scope();
        self.current_function = Some(func.name.clone());

        // Lower parameters
        let params: Vec<HirParam> = func.params.iter()
            .map(|p| self.lower_param(p))
            .collect::<Result<_, _>>()?;

        // Register params in scope
        for param in &params {
            self.define_var(&param.name, param.ty, param.is_mutable);
        }

        // Lower body
        let body = self.lower_block(&func.body)?;

        // Resolve return type
        let return_type = match &func.return_type {
            Some(ty) => self.resolve_type(ty)?,
            None => self.types.intern(Type::Nil),
        };

        let effect = match func.effect {
            Some(Effect::Async) => Effect::Async,
            Some(Effect::Async) => Effect::Async,
            _ => Effect::None,
        };

        self.pop_scope();
        self.current_function = None;

        Ok(HirFunction {
            name: func.name.clone(),
            params,
            return_type,
            body,
            is_public: func.is_public,
            effect,
        })
    }

    fn lower_expr(&mut self, expr: &Expr) -> Result<HirExpr, LowerError> {
        match expr {
            Expr::Integer(n) => {
                let ty = self.types.intern(Type::Int);
                Ok(HirExpr::IntLit(*n, ty))
            }

            Expr::Float(f) => {
                let ty = self.types.intern(Type::Float);
                Ok(HirExpr::FloatLit(*f, ty))
            }

            Expr::Bool(b) => Ok(HirExpr::BoolLit(*b)),

            Expr::String(s) => Ok(HirExpr::StringLit(s.clone())),

            Expr::Identifier(name) => {
                let (ty, _) = self.lookup_var(name)?;
                Ok(HirExpr::Var(name.clone(), ty))
            }

            Expr::Binary { op, left, right } => {
                let left = Box::new(self.lower_expr(left)?);
                let right = Box::new(self.lower_expr(right)?);
                let ty = self.infer_binary_type(op, &left, &right)?;
                Ok(HirExpr::Binary { op: *op, left, right, ty })
            }

            Expr::Call { callee, args } => {
                let callee = Box::new(self.lower_expr(callee)?);
                let args: Vec<HirExpr> = args.iter()
                    .map(|a| self.lower_expr_from_arg(a))
                    .collect::<Result<_, _>>()?;
                let ty = self.infer_call_type(&callee, &args)?;
                Ok(HirExpr::Call { func: callee, args, ty })
            }

            Expr::If { condition, then_branch, else_branch } => {
                let condition = Box::new(self.lower_expr(condition)?);
                let then_branch = self.lower_block_from_expr(then_branch)?;
                let else_branch = else_branch
                    .as_ref()
                    .map(|e| self.lower_block_from_expr(e))
                    .transpose()?;
                let ty = self.infer_if_type(&then_branch, &else_branch)?;
                Ok(HirExpr::If { condition, then_branch, else_branch, ty })
            }

            // ... more expression types
            _ => Err(LowerError::UnsupportedExpr),
        }
    }

    // Helper methods
    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn define_var(&mut self, name: &str, ty: TypeId, is_mutable: bool) {
        if let Some(scope) = self.scope_stack.last_mut() {
            scope.variables.insert(name.to_string(), (ty, is_mutable));
        }
    }

    fn lookup_var(&self, name: &str) -> Result<(TypeId, bool), LowerError> {
        for scope in self.scope_stack.iter().rev() {
            if let Some(&(ty, mutable)) = scope.variables.get(name) {
                return Ok((ty, mutable));
            }
        }
        Err(LowerError::UndefinedVariable(name.to_string()))
    }
}
```

---

## Mid-Level IR (MIR)

### MIR Types (mir/types.rs)

```rust
// crates/compiler/src/mir/types.rs

/// Low-level IR closer to machine code
#[derive(Debug)]
pub struct MirModule {
    pub functions: Vec<MirFunction>,
    pub data: Vec<MirData>,
    pub types: Vec<MirType>,
}

#[derive(Debug)]
pub struct MirFunction {
    pub name: String,
    pub signature: FunctionSignature,
    pub blocks: Vec<BasicBlock>,
    pub locals: Vec<LocalVar>,
    pub is_public: bool,
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub params: Vec<MirType>,
    pub returns: MirType,
    pub calling_conv: CallingConv,
}

#[derive(Debug, Clone, Copy)]
pub enum CallingConv {
    Simple,     // Simple's default calling convention
    C,          // C ABI for FFI
}

#[derive(Debug)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<MirInst>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);

#[derive(Debug)]
pub struct LocalVar {
    pub id: LocalId,
    pub ty: MirType,
    pub name: Option<String>,
}

#[derive(Debug)]
pub enum MirInst {
    // Constants
    ConstInt(LocalId, i64),
    ConstFloat(LocalId, f64),
    ConstBool(LocalId, bool),
    ConstNil(LocalId),

    // Arithmetic
    Add(LocalId, LocalId, LocalId),
    Sub(LocalId, LocalId, LocalId),
    Mul(LocalId, LocalId, LocalId),
    Div(LocalId, LocalId, LocalId),
    Mod(LocalId, LocalId, LocalId),
    Neg(LocalId, LocalId),

    // Comparison
    Eq(LocalId, LocalId, LocalId),
    Ne(LocalId, LocalId, LocalId),
    Lt(LocalId, LocalId, LocalId),
    Le(LocalId, LocalId, LocalId),
    Gt(LocalId, LocalId, LocalId),
    Ge(LocalId, LocalId, LocalId),

    // Logical
    And(LocalId, LocalId, LocalId),
    Or(LocalId, LocalId, LocalId),
    Not(LocalId, LocalId),

    // Memory
    Load(LocalId, LocalId),           // dest, addr
    Store(LocalId, LocalId),          // addr, value
    GetField(LocalId, LocalId, u32),  // dest, base, field_index
    SetField(LocalId, u32, LocalId),  // base, field_index, value
    GetElement(LocalId, LocalId, LocalId),  // dest, base, index
    SetElement(LocalId, LocalId, LocalId),  // base, index, value

    // Allocation
    Alloc(LocalId, MirType),          // Stack allocation
    HeapAlloc(LocalId, MirType),      // GC heap allocation
    RefAlloc(LocalId, MirType),       // Reference-counted allocation

    // Function calls
    Call(LocalId, String, Vec<LocalId>),           // dest, func_name, args
    CallIndirect(LocalId, LocalId, Vec<LocalId>),  // dest, func_ptr, args

    // Type operations
    Cast(LocalId, LocalId, MirType),  // dest, source, target_type
    SizeOf(LocalId, MirType),         // dest, type

    // Move/Copy
    Copy(LocalId, LocalId),           // dest, source
    Move(LocalId, LocalId),           // dest, source (invalidates source)
}

#[derive(Debug)]
pub enum Terminator {
    Return(Option<LocalId>),
    Branch(BlockId),
    CondBranch {
        cond: LocalId,
        then_block: BlockId,
        else_block: BlockId,
    },
    Switch {
        value: LocalId,
        cases: Vec<(i64, BlockId)>,
        default: BlockId,
    },
    Unreachable,
}

#[derive(Debug, Clone)]
pub enum MirType {
    I8, I16, I32, I64,
    F32, F64,
    Bool,
    Ptr(Box<MirType>),
    Struct(Vec<MirType>),
    Array(Box<MirType>, usize),
    Void,
}

#[derive(Debug)]
pub struct MirData {
    pub name: String,
    pub ty: MirType,
    pub init: DataInit,
    pub is_const: bool,
}

#[derive(Debug)]
pub enum DataInit {
    Bytes(Vec<u8>),
    Zero(usize),
    Pointer(String),  // Reference to another symbol
}
```

### HIR to MIR Lowering (mir/lower.rs)

```rust
// crates/compiler/src/mir/lower.rs

use crate::hir::*;
use crate::mir::*;

pub struct MirLowering {
    current_block: BlockId,
    blocks: Vec<BasicBlock>,
    locals: Vec<LocalVar>,
    next_local: u32,
    next_block: u32,
}

impl MirLowering {
    pub fn new() -> Self {
        Self {
            current_block: BlockId(0),
            blocks: Vec::new(),
            locals: Vec::new(),
            next_local: 0,
            next_block: 0,
        }
    }

    pub fn lower_function(&mut self, func: &HirFunction) -> MirFunction {
        self.reset();

        // Create entry block
        let entry = self.create_block();
        self.current_block = entry;

        // Create locals for parameters
        let param_locals: Vec<LocalId> = func.params.iter()
            .map(|p| self.create_local(self.lower_type(&p.ty), Some(p.name.clone())))
            .collect();

        // Lower body
        let result = self.lower_block(&func.body);

        // Add return terminator if needed
        if !self.current_block_terminated() {
            let term = match result {
                Some(local) => Terminator::Return(Some(local)),
                None => Terminator::Return(None),
            };
            self.set_terminator(term);
        }

        MirFunction {
            name: func.name.clone(),
            signature: FunctionSignature {
                params: func.params.iter()
                    .map(|p| self.lower_type(&p.ty))
                    .collect(),
                returns: self.lower_type(&func.return_type),
                calling_conv: CallingConv::Simple,
            },
            blocks: std::mem::take(&mut self.blocks),
            locals: std::mem::take(&mut self.locals),
            is_public: func.is_public,
        }
    }

    fn lower_block(&mut self, block: &HirBlock) -> Option<LocalId> {
        // Lower statements
        for stmt in &block.stmts {
            self.lower_stmt(stmt);
        }

        // Lower final expression
        block.expr.as_ref().map(|e| self.lower_expr(e))
    }

    fn lower_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Let { name, ty, init, is_mutable } => {
                let local = self.create_local(self.lower_type(ty), Some(name.clone()));

                if let Some(init_expr) = init {
                    let init_local = self.lower_expr(init_expr);
                    self.emit(MirInst::Copy(local, init_local));
                }
            }

            HirStmt::Assign { target, value } => {
                let value_local = self.lower_expr(value);
                self.lower_assign(target, value_local);
            }

            HirStmt::Return(expr) => {
                let local = expr.as_ref().map(|e| self.lower_expr(e));
                self.set_terminator(Terminator::Return(local));
            }

            HirStmt::Expr(expr) => {
                self.lower_expr(expr);
            }

            _ => {}
        }
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> LocalId {
        match expr {
            HirExpr::IntLit(n, ty) => {
                let local = self.create_local(self.lower_type(ty), None);
                self.emit(MirInst::ConstInt(local, *n));
                local
            }

            HirExpr::FloatLit(f, ty) => {
                let local = self.create_local(self.lower_type(ty), None);
                self.emit(MirInst::ConstFloat(local, *f));
                local
            }

            HirExpr::BoolLit(b) => {
                let local = self.create_local(MirType::Bool, None);
                self.emit(MirInst::ConstBool(local, *b));
                local
            }

            HirExpr::Binary { op, left, right, ty } => {
                let left_local = self.lower_expr(left);
                let right_local = self.lower_expr(right);
                let result = self.create_local(self.lower_type(ty), None);

                let inst = match op {
                    BinOp::Add => MirInst::Add(result, left_local, right_local),
                    BinOp::Sub => MirInst::Sub(result, left_local, right_local),
                    BinOp::Mul => MirInst::Mul(result, left_local, right_local),
                    BinOp::Div => MirInst::Div(result, left_local, right_local),
                    BinOp::Eq => MirInst::Eq(result, left_local, right_local),
                    BinOp::Ne => MirInst::Ne(result, left_local, right_local),
                    BinOp::Lt => MirInst::Lt(result, left_local, right_local),
                    BinOp::Le => MirInst::Le(result, left_local, right_local),
                    BinOp::Gt => MirInst::Gt(result, left_local, right_local),
                    BinOp::Ge => MirInst::Ge(result, left_local, right_local),
                    BinOp::And => MirInst::And(result, left_local, right_local),
                    BinOp::Or => MirInst::Or(result, left_local, right_local),
                    _ => todo!(),
                };

                self.emit(inst);
                result
            }

            HirExpr::If { condition, then_branch, else_branch, ty } => {
                let cond = self.lower_expr(condition);
                let result = self.create_local(self.lower_type(ty), None);

                let then_block = self.create_block();
                let else_block = self.create_block();
                let merge_block = self.create_block();

                self.set_terminator(Terminator::CondBranch {
                    cond,
                    then_block,
                    else_block,
                });

                // Then branch
                self.current_block = then_block;
                let then_result = self.lower_block(then_branch);
                if let Some(r) = then_result {
                    self.emit(MirInst::Copy(result, r));
                }
                self.set_terminator(Terminator::Branch(merge_block));

                // Else branch
                self.current_block = else_block;
                if let Some(else_branch) = else_branch {
                    let else_result = self.lower_block(else_branch);
                    if let Some(r) = else_result {
                        self.emit(MirInst::Copy(result, r));
                    }
                }
                self.set_terminator(Terminator::Branch(merge_block));

                self.current_block = merge_block;
                result
            }

            HirExpr::Call { func, args, ty } => {
                let arg_locals: Vec<LocalId> = args.iter()
                    .map(|a| self.lower_expr(a))
                    .collect();
                let result = self.create_local(self.lower_type(ty), None);

                // Get function name (simplified)
                if let HirExpr::Var(name, _) = func.as_ref() {
                    self.emit(MirInst::Call(result, name.clone(), arg_locals));
                }

                result
            }

            // ... more expressions
            _ => {
                let local = self.create_local(MirType::Void, None);
                local
            }
        }
    }

    // Helper methods
    fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.blocks.push(BasicBlock {
            id,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        });
        id
    }

    fn create_local(&mut self, ty: MirType, name: Option<String>) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        self.locals.push(LocalVar { id, ty, name });
        id
    }

    fn emit(&mut self, inst: MirInst) {
        let block = &mut self.blocks[self.current_block.0 as usize];
        block.instructions.push(inst);
    }

    fn set_terminator(&mut self, term: Terminator) {
        let block = &mut self.blocks[self.current_block.0 as usize];
        block.terminator = term;
    }

    fn lower_type(&self, ty: &TypeId) -> MirType {
        // TODO: Look up in type table
        MirType::I64
    }

    fn reset(&mut self) {
        self.blocks.clear();
        self.locals.clear();
        self.next_local = 0;
        self.next_block = 0;
    }
}
```

---

## Code Generation with Cranelift

### Cranelift Backend (codegen/cranelift.rs)

```rust
// crates/compiler/src/codegen/cranelift.rs

use cranelift::prelude::*;
use cranelift_module::{Module, Linkage, FuncId};
use cranelift_object::{ObjectBuilder, ObjectModule};

use crate::mir::*;

pub struct CraneliftCodegen {
    module: ObjectModule,
    ctx: codegen::Context,
    func_ids: HashMap<String, FuncId>,
}

impl CraneliftCodegen {
    pub fn new(target: &str) -> Result<Self, String> {
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").unwrap();

        let isa_builder = cranelift_native::builder()
            .map_err(|e| format!("ISA error: {}", e))?;
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .map_err(|e| format!("ISA finish error: {}", e))?;

        let builder = ObjectBuilder::new(
            isa,
            "simple_module",
            cranelift_module::default_libcall_names(),
        )
        .map_err(|e| format!("ObjectBuilder error: {}", e))?;

        let module = ObjectModule::new(builder);

        Ok(Self {
            module,
            ctx: module.make_context(),
            func_ids: HashMap::new(),
        })
    }

    pub fn compile_module(&mut self, mir: &MirModule) -> Result<Vec<u8>, String> {
        // Declare all functions first
        for func in &mir.functions {
            let sig = self.translate_signature(&func.signature);
            let linkage = if func.is_public {
                Linkage::Export
            } else {
                Linkage::Local
            };

            let id = self.module
                .declare_function(&func.name, linkage, &sig)
                .map_err(|e| format!("Declare error: {}", e))?;

            self.func_ids.insert(func.name.clone(), id);
        }

        // Compile each function
        for func in &mir.functions {
            self.compile_function(func)?;
        }

        // Finish and get object code
        let product = self.module.finish();
        Ok(product.emit().map_err(|e| format!("Emit error: {}", e))?)
    }

    fn compile_function(&mut self, func: &MirFunction) -> Result<(), String> {
        let func_id = self.func_ids[&func.name];

        self.ctx.func.signature = self.translate_signature(&func.signature);
        self.ctx.func.name = ExternalName::user(0, func_id.as_u32());

        let mut builder_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut builder_ctx);

        // Create entry block
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Map MIR blocks to Cranelift blocks
        let mut block_map: HashMap<BlockId, Block> = HashMap::new();
        block_map.insert(BlockId(0), entry_block);

        for mir_block in &func.blocks[1..] {
            let cl_block = builder.create_block();
            block_map.insert(mir_block.id, cl_block);
        }

        // Map MIR locals to Cranelift variables
        let mut var_map: HashMap<LocalId, Variable> = HashMap::new();
        for (i, local) in func.locals.iter().enumerate() {
            let var = Variable::new(i);
            let ty = self.translate_type(&local.ty);
            builder.declare_var(var, ty);
            var_map.insert(local.id, var);
        }

        // Translate each block
        for mir_block in &func.blocks {
            if mir_block.id != BlockId(0) {
                builder.switch_to_block(block_map[&mir_block.id]);
            }

            // Translate instructions
            for inst in &mir_block.instructions {
                self.translate_instruction(&mut builder, inst, &var_map)?;
            }

            // Translate terminator
            self.translate_terminator(&mut builder, &mir_block.terminator, &block_map, &var_map)?;
        }

        builder.seal_all_blocks();
        builder.finalize();

        // Compile and define
        self.module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| format!("Define error: {}", e))?;

        self.module.clear_context(&mut self.ctx);
        Ok(())
    }

    fn translate_instruction(
        &self,
        builder: &mut FunctionBuilder,
        inst: &MirInst,
        vars: &HashMap<LocalId, Variable>,
    ) -> Result<(), String> {
        match inst {
            MirInst::ConstInt(dest, value) => {
                let val = builder.ins().iconst(types::I64, *value);
                builder.def_var(vars[dest], val);
            }

            MirInst::ConstFloat(dest, value) => {
                let val = builder.ins().f64const(*value);
                builder.def_var(vars[dest], val);
            }

            MirInst::ConstBool(dest, value) => {
                let val = builder.ins().iconst(types::I8, *value as i64);
                builder.def_var(vars[dest], val);
            }

            MirInst::Add(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().iadd(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Sub(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().isub(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Mul(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().imul(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Div(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let result = builder.ins().sdiv(l, r);
                builder.def_var(vars[dest], result);
            }

            MirInst::Lt(dest, left, right) => {
                let l = builder.use_var(vars[left]);
                let r = builder.use_var(vars[right]);
                let cmp = builder.ins().icmp(IntCC::SignedLessThan, l, r);
                builder.def_var(vars[dest], cmp);
            }

            MirInst::Call(dest, name, args) => {
                let func_id = self.func_ids.get(name)
                    .ok_or_else(|| format!("Unknown function: {}", name))?;
                let func_ref = self.module.declare_func_in_func(*func_id, builder.func);

                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| builder.use_var(vars[a]))
                    .collect();

                let call = builder.ins().call(func_ref, &arg_vals);
                let results = builder.inst_results(call);
                if !results.is_empty() {
                    builder.def_var(vars[dest], results[0]);
                }
            }

            MirInst::Copy(dest, src) => {
                let val = builder.use_var(vars[src]);
                builder.def_var(vars[dest], val);
            }

            // ... more instructions
            _ => {}
        }

        Ok(())
    }

    fn translate_terminator(
        &self,
        builder: &mut FunctionBuilder,
        term: &Terminator,
        blocks: &HashMap<BlockId, Block>,
        vars: &HashMap<LocalId, Variable>,
    ) -> Result<(), String> {
        match term {
            Terminator::Return(Some(local)) => {
                let val = builder.use_var(vars[local]);
                builder.ins().return_(&[val]);
            }

            Terminator::Return(None) => {
                builder.ins().return_(&[]);
            }

            Terminator::Branch(target) => {
                builder.ins().jump(blocks[target], &[]);
            }

            Terminator::CondBranch { cond, then_block, else_block } => {
                let cond_val = builder.use_var(vars[cond]);
                builder.ins().brif(cond_val, blocks[then_block], &[], blocks[else_block], &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(TrapCode::UnreachableCodeReached);
            }

            _ => {}
        }

        Ok(())
    }

    fn translate_signature(&self, sig: &FunctionSignature) -> Signature {
        let mut cl_sig = Signature::new(CallConv::SystemV);

        for param in &sig.params {
            cl_sig.params.push(AbiParam::new(self.translate_type(param)));
        }

        if sig.returns != MirType::Void {
            cl_sig.returns.push(AbiParam::new(self.translate_type(&sig.returns)));
        }

        cl_sig
    }

    fn translate_type(&self, ty: &MirType) -> types::Type {
        match ty {
            MirType::I8 => types::I8,
            MirType::I16 => types::I16,
            MirType::I32 => types::I32,
            MirType::I64 => types::I64,
            MirType::F32 => types::F32,
            MirType::F64 => types::F64,
            MirType::Bool => types::I8,
            MirType::Ptr(_) => types::I64,  // Pointer is 64-bit
            MirType::Void => types::I64,    // Placeholder
            _ => types::I64,
        }
    }
}
```

---

## SMF Linker

### SMF Emission (linker/emit.rs)

```rust
// crates/compiler/src/linker/emit.rs

use std::io::Write;
use crate::smf::*;

pub struct SmfEmitter {
    header: SmfHeader,
    sections: Vec<(SmfSection, Vec<u8>)>,
    symbols: Vec<SmfSymbol>,
    string_table: Vec<u8>,
    relocations: Vec<SmfRelocation>,
}

impl SmfEmitter {
    pub fn new() -> Self {
        Self {
            header: SmfHeader::default(),
            sections: Vec::new(),
            symbols: Vec::new(),
            string_table: vec![0],  // Start with null byte
            relocations: Vec::new(),
        }
    }

    pub fn set_executable(&mut self, entry_offset: u64) {
        self.header.flags |= SMF_FLAG_EXECUTABLE;
        self.header.entry_point = entry_offset;
    }

    pub fn set_reloadable(&mut self) {
        self.header.flags |= SMF_FLAG_RELOADABLE;
    }

    pub fn add_code(&mut self, code: Vec<u8>) {
        let section = SmfSection {
            section_type: SectionType::Code,
            flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
            offset: 0,  // Filled in during emit
            size: code.len() as u64,
            virtual_size: code.len() as u64,
            alignment: 16,
            name: *b".text\0\0\0\0\0\0\0\0\0\0\0",
        };
        self.sections.push((section, code));
    }

    pub fn add_data(&mut self, data: Vec<u8>, readonly: bool) {
        let section = SmfSection {
            section_type: if readonly { SectionType::RoData } else { SectionType::Data },
            flags: SECTION_FLAG_READ | if readonly { 0 } else { SECTION_FLAG_WRITE },
            offset: 0,
            size: data.len() as u64,
            virtual_size: data.len() as u64,
            alignment: 8,
            name: if readonly {
                *b".rodata\0\0\0\0\0\0\0\0\0"
            } else {
                *b".data\0\0\0\0\0\0\0\0\0\0\0"
            },
        };
        self.sections.push((section, data));
    }

    pub fn add_symbol(&mut self, name: &str, sym_type: SymbolType, binding: SymbolBinding, value: u64, size: u64) {
        let name_offset = self.string_table.len() as u32;
        self.string_table.extend_from_slice(name.as_bytes());
        self.string_table.push(0);

        self.symbols.push(SmfSymbol {
            name_offset,
            name_hash: hash_name(name),
            sym_type,
            binding,
            visibility: 0,
            flags: 0,
            value,
            size,
            type_id: 0,
            version: 1,
        });
    }

    pub fn add_relocation(&mut self, offset: u64, symbol_index: u32, reloc_type: RelocationType, addend: i64) {
        self.relocations.push(SmfRelocation {
            offset,
            symbol_index,
            reloc_type,
            addend,
        });
    }

    pub fn emit<W: Write>(&mut self, writer: &mut W) -> std::io::Result<()> {
        // Calculate offsets
        let mut offset = SmfHeader::SIZE as u64;

        // Section table offset
        self.header.section_table_offset = offset;
        self.header.section_count = self.sections.len() as u32;
        offset += (self.sections.len() * std::mem::size_of::<SmfSection>()) as u64;

        // Update section offsets
        for (section, data) in &mut self.sections {
            // Align
            let alignment = section.alignment as u64;
            offset = (offset + alignment - 1) & !(alignment - 1);
            section.offset = offset;
            offset += data.len() as u64;
        }

        // Relocation section
        if !self.relocations.is_empty() {
            let reloc_size = (self.relocations.len() * std::mem::size_of::<SmfRelocation>()) as u64;
            let reloc_section = SmfSection {
                section_type: SectionType::Reloc,
                flags: SECTION_FLAG_READ,
                offset,
                size: reloc_size,
                virtual_size: reloc_size,
                alignment: 8,
                name: *b".reloc\0\0\0\0\0\0\0\0\0\0",
            };
            offset += reloc_size;
            // Add relocation section (data will be written separately)
        }

        // Symbol table
        self.header.symbol_table_offset = offset;
        self.header.symbol_count = self.symbols.len() as u32;
        offset += (self.symbols.len() * std::mem::size_of::<SmfSymbol>()) as u64;

        // String table follows symbols
        offset += self.string_table.len() as u64;

        // Write header
        self.header.magic = *SMF_MAGIC;
        self.header.version_major = 1;
        self.header.version_minor = 0;

        #[cfg(target_os = "linux")]
        { self.header.platform = Platform::Linux as u8; }
        #[cfg(target_os = "windows")]
        { self.header.platform = Platform::Windows as u8; }

        #[cfg(target_arch = "x86_64")]
        { self.header.arch = Arch::X86_64 as u8; }

        writer.write_all(as_bytes(&self.header))?;

        // Write section table
        for (section, _) in &self.sections {
            writer.write_all(as_bytes(section))?;
        }

        // Write section data
        for (section, data) in &self.sections {
            // Padding for alignment
            let current_pos = SmfHeader::SIZE
                + self.sections.len() * std::mem::size_of::<SmfSection>();
            let target_pos = section.offset as usize;
            let padding = target_pos.saturating_sub(current_pos);
            writer.write_all(&vec![0u8; padding])?;

            writer.write_all(data)?;
        }

        // Write relocations
        for reloc in &self.relocations {
            writer.write_all(as_bytes(reloc))?;
        }

        // Write symbols
        for sym in &self.symbols {
            writer.write_all(as_bytes(sym))?;
        }

        // Write string table
        writer.write_all(&self.string_table)?;

        Ok(())
    }
}

fn as_bytes<T>(value: &T) -> &[u8] {
    unsafe {
        std::slice::from_raw_parts(
            value as *const T as *const u8,
            std::mem::size_of::<T>(),
        )
    }
}
```

---

## Compilation Pipeline

```rust
// crates/compiler/src/pipeline.rs

use std::path::Path;
use std::fs::File;
use std::io::BufWriter;

use crate::parser::SimpleParser;
use crate::hir::HirLowering;
use crate::mir::MirLowering;
use crate::codegen::CraneliftCodegen;
use crate::linker::SmfEmitter;
use crate::cache::CompilationCache;

pub struct CompilerPipeline {
    parser: SimpleParser,
    cache: CompilationCache,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, String> {
        Ok(Self {
            parser: SimpleParser::new()?,
            cache: CompilationCache::new(),
        })
    }

    /// Compile source file to SMF
    pub fn compile(&mut self, source_path: &Path, output_path: &Path) -> Result<(), CompileError> {
        // Check cache
        let source_hash = self.cache.hash_file(source_path)?;
        if let Some(cached) = self.cache.get(source_path, source_hash) {
            std::fs::copy(&cached, output_path)?;
            return Ok(());
        }

        // Read source
        let source = std::fs::read_to_string(source_path)?;

        // Parse
        let ast = self.parser.parse(&source)?;

        // Lower to HIR
        let mut hir_lower = HirLowering::new();
        let hir = hir_lower.lower_module(&ast)?;

        // Lower to MIR
        let mut mir_lower = MirLowering::new();
        let mir = mir_lower.lower_module(&hir)?;

        // Generate code
        let mut codegen = CraneliftCodegen::new("x86_64")?;
        let object_code = codegen.compile_module(&mir)?;

        // Emit SMF
        let mut emitter = SmfEmitter::new();
        emitter.add_code(object_code);

        // Add symbols
        for func in &mir.functions {
            emitter.add_symbol(
                &func.name,
                SymbolType::Function,
                if func.is_public { SymbolBinding::Global } else { SymbolBinding::Local },
                0,  // TODO: Calculate offset
                0,
            );
        }

        // Check for main function
        if mir.functions.iter().any(|f| f.name == "main") {
            emitter.set_executable(0);  // TODO: Calculate main offset
        }

        // Write output
        let file = File::create(output_path)?;
        let mut writer = BufWriter::new(file);
        emitter.emit(&mut writer)?;

        // Update cache
        self.cache.store(source_path, source_hash, output_path)?;

        Ok(())
    }

    /// Compile and run (interpreter-like workflow)
    pub fn compile_and_run(&mut self, source_path: &Path) -> Result<i32, CompileError> {
        // Determine output path
        let output_path = source_path.with_extension("smf");

        // Compile if needed
        if self.needs_recompile(source_path, &output_path)? {
            self.compile(source_path, &output_path)?;
        }

        // Load and run
        let loader = crate::loader::ModuleLoader::new();
        let module = loader.load(&output_path)?;

        // Get entry point
        type MainFn = extern "C" fn() -> i32;
        let main: MainFn = module.entry_point()
            .ok_or(CompileError::NoEntryPoint)?;

        Ok(main())
    }

    fn needs_recompile(&self, source: &Path, output: &Path) -> Result<bool, CompileError> {
        if !output.exists() {
            return Ok(true);
        }

        let source_modified = source.metadata()?.modified()?;
        let output_modified = output.metadata()?.modified()?;

        Ok(source_modified > output_modified)
    }
}

#[derive(Debug)]
pub enum CompileError {
    Io(std::io::Error),
    Parse(String),
    Lower(String),
    Codegen(String),
    Link(String),
    NoEntryPoint,
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-compiler"
version = "0.1.0"
edition = "2021"

[dependencies]
cranelift = "0.107"
cranelift-codegen = "0.107"
cranelift-module = "0.107"
cranelift-object = "0.107"
cranelift-native = "0.107"
target-lexicon = "0.12"

simple-parser = { path = "../parser" }
simple-loader = { path = "../loader" }
```

---

## Summary

| Stage | Input | Output | Purpose |
|-------|-------|--------|---------|
| Parser | Source (.simple) | AST | Syntax analysis |
| HIR Lowering | AST | HIR | Type checking, desugaring |
| MIR Lowering | HIR | MIR | Control flow, basic blocks |
| Codegen | MIR | Object code | Native code generation |
| Linker | Object code | SMF | Package into loadable module |

This pipeline enables the interpreter-like workflow: source changes trigger automatic recompilation before execution.
