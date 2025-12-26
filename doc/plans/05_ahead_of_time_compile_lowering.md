# AOT Compilation: AST to HIR and MIR Types

Part of [Ahead of Time Compilation Plan](05_ahead_of_time_compile.md).

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

---

Next: [HIR to MIR and Cranelift](05_ahead_of_time_compile_codegen.md)
