use simple_parser::ast::{BinOp, Expr, Node, Pattern, PointerKind, Type as AstType};
use std::collections::HashMap;

//==============================================================================
// Pure Type Inference (for formal verification)
//==============================================================================
// This module provides a pure, total inference function that maps directly to
// the Lean 4 formal verification model in `verification/type_inference_compile/`.
//
// The Lean model is:
//   def infer : Expr → Option Ty
//     | litNat _ => some Ty.nat
//     | litBool _ => some Ty.bool
//     | add a b => do
//         let Ty.nat ← infer a | none
//         let Ty.nat ← infer b | none
//         pure Ty.nat
//     | ifElse c t e => do
//         let Ty.bool ← infer c | none
//         let τt ← infer t
//         let τe ← infer e
//         if τt = τe then pure τt else none
//
// Key property: Determinism - inference returns at most one type.

//==============================================================================
// LeanTy / LeanExpr - Exact match to TypeInferenceCompile.lean
//==============================================================================
// These types match the Lean model EXACTLY with no extensions.
//
// Lean equivalent:
// ```lean
// inductive Ty
//   | nat
//   | bool
//   | arrow (a b : Ty)
//   deriving DecidableEq, Repr
//
// inductive Expr
//   | litNat (n : Nat)
//   | litBool (b : Bool)
//   | add (a b : Expr)
//   | ifElse (c t e : Expr)
//   | lam (body : Expr)
//   | app (f x : Expr)
//   deriving Repr
// ```

/// Type matching TypeInferenceCompile.lean exactly (3 variants, no Str).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanTy {
    /// Natural number type
    Nat,
    /// Boolean type
    Bool,
    /// Function type (arrow)
    Arrow(Box<LeanTy>, Box<LeanTy>),
}

/// Expression matching TypeInferenceCompile.lean exactly (6 variants).
#[derive(Debug, Clone, PartialEq)]
pub enum LeanExpr {
    /// Natural number literal (Nat, not i64)
    LitNat(u64),
    /// Boolean literal
    LitBool(bool),
    /// Addition
    Add(Box<LeanExpr>, Box<LeanExpr>),
    /// If-then-else
    IfElse(Box<LeanExpr>, Box<LeanExpr>, Box<LeanExpr>),
    /// Lambda (toy rule: abstracts Nat argument)
    Lam(Box<LeanExpr>),
    /// Application
    App(Box<LeanExpr>, Box<LeanExpr>),
}

/// Lean: def infer : Expr → Option Ty
///
/// Pure type inference function matching Lean exactly.
/// This is a total function returning Option.
pub fn lean_infer(expr: &LeanExpr) -> Option<LeanTy> {
    match expr {
        LeanExpr::LitNat(_) => Some(LeanTy::Nat),
        LeanExpr::LitBool(_) => Some(LeanTy::Bool),

        LeanExpr::Add(a, b) => {
            // Lean: let Ty.nat ← infer a | none; let Ty.nat ← infer b | none; pure Ty.nat
            match (lean_infer(a)?, lean_infer(b)?) {
                (LeanTy::Nat, LeanTy::Nat) => Some(LeanTy::Nat),
                _ => None,
            }
        }

        LeanExpr::IfElse(c, t, e) => {
            // Lean: let Ty.bool ← infer c | none
            let cond_ty = lean_infer(c)?;
            if cond_ty != LeanTy::Bool {
                return None;
            }
            let then_ty = lean_infer(t)?;
            let else_ty = lean_infer(e)?;
            // Lean: if τt = τe then pure τt else none
            if then_ty == else_ty {
                Some(then_ty)
            } else {
                None
            }
        }

        LeanExpr::Lam(body) => {
            // Lean: τ.map fun t => Ty.arrow Ty.nat t
            let body_ty = lean_infer(body)?;
            Some(LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(body_ty)))
        }

        LeanExpr::App(f, x) => {
            // Lean: match ← infer f with | Ty.arrow a b => ...
            match lean_infer(f)? {
                LeanTy::Arrow(arg_ty, ret_ty) => {
                    let x_ty = lean_infer(x)?;
                    if x_ty == *arg_ty {
                        Some(*ret_ty)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
    }
}

/// Lean: theorem infer_deterministic (e : Expr) (t₁ t₂ : Ty) :
///   infer e = some t₁ → infer e = some t₂ → t₁ = t₂
///
/// This function encodes the determinism theorem as a runtime assertion.
/// For any expression, inference returns at most one type.
pub fn infer_deterministic(e: &LeanExpr) -> bool {
    // Since infer is a pure function, calling it twice must give the same result
    let t1 = lean_infer(e);
    let t2 = lean_infer(e);
    t1 == t2
}

//==============================================================================
// SimpleTy / SimpleExpr - Extended for Rust convenience
//==============================================================================

/// Simple type for pure inference (maps to Lean's Ty with Str extension).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpleTy {
    Nat,
    Bool,
    Str,
    Arrow(Box<SimpleTy>, Box<SimpleTy>),
}

impl SimpleTy {
    /// Convert to LeanTy if possible (Str has no Lean equivalent).
    pub fn to_lean(&self) -> Option<LeanTy> {
        match self {
            SimpleTy::Nat => Some(LeanTy::Nat),
            SimpleTy::Bool => Some(LeanTy::Bool),
            SimpleTy::Str => None, // No Lean equivalent
            SimpleTy::Arrow(a, b) => Some(LeanTy::Arrow(
                Box::new(a.to_lean()?),
                Box::new(b.to_lean()?),
            )),
        }
    }
}

/// Simple expression for pure inference (maps to Lean's Expr with Str extension).
#[derive(Debug, Clone)]
pub enum SimpleExpr {
    LitNat(i64),
    LitBool(bool),
    LitStr(String),
    Add(Box<SimpleExpr>, Box<SimpleExpr>),
    IfElse(Box<SimpleExpr>, Box<SimpleExpr>, Box<SimpleExpr>),
    Lam(Box<SimpleExpr>),
    App(Box<SimpleExpr>, Box<SimpleExpr>),
}

impl SimpleExpr {
    /// Convert to LeanExpr if possible (LitStr and negative numbers have no Lean equivalent).
    pub fn to_lean(&self) -> Option<LeanExpr> {
        match self {
            SimpleExpr::LitNat(n) if *n >= 0 => Some(LeanExpr::LitNat(*n as u64)),
            SimpleExpr::LitNat(_) => None, // Negative numbers not in Lean Nat
            SimpleExpr::LitBool(b) => Some(LeanExpr::LitBool(*b)),
            SimpleExpr::LitStr(_) => None, // No Lean equivalent
            SimpleExpr::Add(a, b) => Some(LeanExpr::Add(
                Box::new(a.to_lean()?),
                Box::new(b.to_lean()?),
            )),
            SimpleExpr::IfElse(c, t, e) => Some(LeanExpr::IfElse(
                Box::new(c.to_lean()?),
                Box::new(t.to_lean()?),
                Box::new(e.to_lean()?),
            )),
            SimpleExpr::Lam(body) => Some(LeanExpr::Lam(Box::new(body.to_lean()?))),
            SimpleExpr::App(f, x) => Some(LeanExpr::App(
                Box::new(f.to_lean()?),
                Box::new(x.to_lean()?),
            )),
        }
    }
}

/// Pure type inference function.
/// Returns `Some(ty)` if inference succeeds, `None` otherwise.
/// This is a total function, corresponding to Lean's `infer : Expr → Option Ty`.
///
/// Determinism theorem (proven in Lean):
///   infer e = some t₁ → infer e = some t₂ → t₁ = t₂
pub fn infer_simple(expr: &SimpleExpr) -> Option<SimpleTy> {
    match expr {
        SimpleExpr::LitNat(_) => Some(SimpleTy::Nat),
        SimpleExpr::LitBool(_) => Some(SimpleTy::Bool),
        SimpleExpr::LitStr(_) => Some(SimpleTy::Str),

        SimpleExpr::Add(a, b) => {
            // Both operands must be Nat
            match (infer_simple(a)?, infer_simple(b)?) {
                (SimpleTy::Nat, SimpleTy::Nat) => Some(SimpleTy::Nat),
                _ => None,
            }
        }

        SimpleExpr::IfElse(cond, then_br, else_br) => {
            // Condition must be Bool, branches must have same type
            let cond_ty = infer_simple(cond)?;
            if cond_ty != SimpleTy::Bool {
                return None;
            }
            let then_ty = infer_simple(then_br)?;
            let else_ty = infer_simple(else_br)?;
            if then_ty == else_ty {
                Some(then_ty)
            } else {
                None
            }
        }

        SimpleExpr::Lam(body) => {
            // Toy rule: lambda abstracts a Nat argument
            let body_ty = infer_simple(body)?;
            Some(SimpleTy::Arrow(Box::new(SimpleTy::Nat), Box::new(body_ty)))
        }

        SimpleExpr::App(f, x) => match infer_simple(f)? {
            SimpleTy::Arrow(arg_ty, ret_ty) => {
                let x_ty = infer_simple(x)?;
                if x_ty == *arg_ty {
                    Some(*ret_ty)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

/// Convert a full AST expression to a simple expression for pure inference.
/// Returns `None` if the expression uses features not in the simple model.
pub fn to_simple_expr(expr: &Expr) -> Option<SimpleExpr> {
    match expr {
        Expr::Integer(n) => Some(SimpleExpr::LitNat(*n)),
        Expr::Bool(b) => Some(SimpleExpr::LitBool(*b)),
        Expr::String(s) => Some(SimpleExpr::LitStr(s.clone())),

        Expr::Binary {
            left,
            right,
            op: BinOp::Add,
        } => {
            let l = to_simple_expr(left)?;
            let r = to_simple_expr(right)?;
            Some(SimpleExpr::Add(Box::new(l), Box::new(r)))
        }

        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let c = to_simple_expr(condition)?;
            let t = to_simple_expr(then_branch)?;
            let e = to_simple_expr(else_branch.as_ref()?)?;
            Some(SimpleExpr::IfElse(Box::new(c), Box::new(t), Box::new(e)))
        }

        // Other expressions are not in the simple model
        _ => None,
    }
}

/// Pure inference on AST expressions (when possible).
/// Falls back to `None` for complex expressions.
pub fn infer_pure(expr: &Expr) -> Option<SimpleTy> {
    to_simple_expr(expr).and_then(|e| infer_simple(&e))
}

//==============================================================================
// Full Type System
//==============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Bool,
    Str,
    Float,
    Nil,
    Var(usize),
    Function {
        params: Vec<Type>,
        ret: Box<Type>,
    },
    Array(Box<Type>),
    /// Union type: A | B | C - value can be any of the member types
    Union(Vec<Type>),
    /// Generic type: Type<A, B> - parameterized type
    Generic {
        name: String,
        args: Vec<Type>,
    },
    /// Type parameter: T, U, etc. - placeholder for generic instantiation
    TypeParam(String),
    /// Named type reference (struct, class, enum name)
    Named(String),
    /// Tuple type: (A, B, C)
    Tuple(Vec<Type>),
    /// Dictionary type: {K: V}
    Dict {
        key: Box<Type>,
        value: Box<Type>,
    },
    /// Optional type: T?
    Optional(Box<Type>),
    /// Immutable borrow: &T - reference that allows read-only access
    Borrow(Box<Type>),
    /// Mutable borrow: &mut T - reference that allows read-write access
    BorrowMut(Box<Type>),
    /// Constructor type: Constructor[T] - a constructor that produces T
    Constructor {
        target: Box<Type>,
        args: Option<Vec<Type>>,
    },
    /// SIMD vector type: vec[N, T]
    Simd {
        lanes: u32,
        element: Box<Type>,
    },
}

impl Type {
    /// Apply substitution to this type
    pub fn apply_subst(&self, subst: &Substitution) -> Type {
        match self {
            Type::Var(id) => {
                if let Some(ty) = subst.get(*id) {
                    ty.apply_subst(subst)
                } else {
                    self.clone()
                }
            }
            Type::Function { params, ret } => Type::Function {
                params: params.iter().map(|p| p.apply_subst(subst)).collect(),
                ret: Box::new(ret.apply_subst(subst)),
            },
            Type::Array(elem) => Type::Array(Box::new(elem.apply_subst(subst))),
            Type::Union(types) => Type::Union(types.iter().map(|t| t.apply_subst(subst)).collect()),
            Type::Generic { name, args } => Type::Generic {
                name: name.clone(),
                args: args.iter().map(|a| a.apply_subst(subst)).collect(),
            },
            Type::Tuple(types) => Type::Tuple(types.iter().map(|t| t.apply_subst(subst)).collect()),
            Type::Dict { key, value } => Type::Dict {
                key: Box::new(key.apply_subst(subst)),
                value: Box::new(value.apply_subst(subst)),
            },
            Type::Optional(inner) => Type::Optional(Box::new(inner.apply_subst(subst))),
            Type::Borrow(inner) => Type::Borrow(Box::new(inner.apply_subst(subst))),
            Type::BorrowMut(inner) => Type::BorrowMut(Box::new(inner.apply_subst(subst))),
            Type::Simd { lanes, element } => Type::Simd {
                lanes: *lanes,
                element: Box::new(element.apply_subst(subst)),
            },
            _ => self.clone(),
        }
    }

    /// Check if this type contains the given type variable
    pub fn contains_var(&self, var_id: usize) -> bool {
        match self {
            Type::Var(id) => *id == var_id,
            Type::Function { params, ret } => {
                params.iter().any(|p| p.contains_var(var_id)) || ret.contains_var(var_id)
            }
            Type::Array(elem) => elem.contains_var(var_id),
            Type::Union(types) => types.iter().any(|t| t.contains_var(var_id)),
            Type::Generic { args, .. } => args.iter().any(|a| a.contains_var(var_id)),
            Type::Tuple(types) => types.iter().any(|t| t.contains_var(var_id)),
            Type::Dict { key, value } => key.contains_var(var_id) || value.contains_var(var_id),
            Type::Optional(inner) => inner.contains_var(var_id),
            Type::Borrow(inner) => inner.contains_var(var_id),
            Type::BorrowMut(inner) => inner.contains_var(var_id),
            Type::Simd { element, .. } => element.contains_var(var_id),
            _ => false,
        }
    }
}

/// Substitution map for type variables
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    map: HashMap<usize, Type>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn get(&self, id: usize) -> Option<&Type> {
        self.map.get(&id)
    }

    pub fn insert(&mut self, id: usize, ty: Type) {
        self.map.insert(id, ty);
    }

    /// Compose two substitutions: self ∘ other
    pub fn compose(&mut self, other: &Substitution) {
        // Apply self to all types in other
        for (id, ty) in &other.map {
            let new_ty = ty.apply_subst(self);
            self.map.insert(*id, new_ty);
        }
    }
}

#[derive(Debug)]
pub enum TypeError {
    Mismatch { expected: Type, found: Type },
    Undefined(String),
    OccursCheck { var_id: usize, ty: Type },
    Other(String),
}

pub struct TypeChecker {
    env: HashMap<String, Type>,
    next_var: usize,
    /// Type parameter environment for generics
    type_params: HashMap<String, Type>,
    /// Substitution map for type inference
    subst: Substitution,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut tc = Self {
            env: HashMap::new(),
            next_var: 0,
            type_params: HashMap::new(),
            subst: Substitution::new(),
        };
        // Add built-in functions to environment
        tc.add_builtins();
        tc
    }

    /// Add built-in functions to the type environment
    fn add_builtins(&mut self) {
        // Generate fresh vars first to avoid borrow issues
        let var1 = self.fresh_var();
        let var2 = self.fresh_var();
        let var3 = self.fresh_var();
        let var4 = self.fresh_var();
        let var5 = self.fresh_var();
        let var6 = self.fresh_var();
        let var7 = self.fresh_var();
        let var8 = self.fresh_var();
        let var9 = self.fresh_var();
        let var10 = self.fresh_var();
        let var11 = self.fresh_var();
        let var12 = self.fresh_var();
        let var13 = self.fresh_var();

        // Generic function type (takes any, returns any)
        let generic_fn = Type::Function {
            params: vec![var1.clone()],
            ret: Box::new(var2),
        };

        // Concurrency functions
        self.env.insert("spawn".to_string(), generic_fn.clone());
        self.env.insert("spawn_isolated".to_string(), generic_fn.clone());
        self.env.insert("async".to_string(), generic_fn.clone());
        self.env.insert("future".to_string(), generic_fn.clone());
        self.env.insert("await".to_string(), generic_fn.clone());
        self.env.insert(
            "is_ready".to_string(),
            Type::Function {
                params: vec![var3],
                ret: Box::new(Type::Bool),
            },
        );

        // Actor functions
        self.env.insert(
            "send".to_string(),
            Type::Function {
                params: vec![var4, var5],
                ret: Box::new(Type::Nil),
            },
        );
        self.env.insert("recv".to_string(), generic_fn.clone());
        self.env.insert(
            "reply".to_string(),
            Type::Function {
                params: vec![var6],
                ret: Box::new(Type::Nil),
            },
        );
        self.env.insert(
            "join".to_string(),
            Type::Function {
                params: vec![var7],
                ret: Box::new(Type::Nil),
            },
        );

        // Common built-in functions
        self.env.insert(
            "len".to_string(),
            Type::Function {
                params: vec![var8],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert("print".to_string(), generic_fn.clone());
        self.env.insert("println".to_string(), generic_fn.clone());
        // Channel type constructor
        self.env.insert("Channel".to_string(), generic_fn.clone());
        // ThreadPool constructor
        self.env.insert("ThreadPool".to_string(), generic_fn.clone());
        self.env.insert(
            "type".to_string(),
            Type::Function {
                params: vec![var9],
                ret: Box::new(Type::Str),
            },
        );
        self.env.insert(
            "str".to_string(),
            Type::Function {
                params: vec![var10],
                ret: Box::new(Type::Str),
            },
        );
        self.env.insert(
            "int".to_string(),
            Type::Function {
                params: vec![var11],
                ret: Box::new(Type::Int),
            },
        );

        // Math functions (extern)
        self.env.insert(
            "abs".to_string(),
            Type::Function {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "sqrt".to_string(),
            Type::Function {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "pow".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "min".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "max".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );

        // Generator/coroutine functions
        self.env.insert("generator".to_string(), generic_fn.clone());
        self.env.insert("next".to_string(), generic_fn.clone());
        self.env.insert("collect".to_string(), generic_fn.clone());

        // Use remaining vars for reserved names
        let _ = (var12, var13);
    }

    /// Unify two types, updating the substitution
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        let t1 = t1.apply_subst(&self.subst);
        let t2 = t2.apply_subst(&self.subst);

        match (&t1, &t2) {
            // Same types unify
            (Type::Int, Type::Int) => Ok(()),
            (Type::Float, Type::Float) => Ok(()),
            (Type::Bool, Type::Bool) => Ok(()),
            (Type::Str, Type::Str) => Ok(()),
            (Type::Nil, Type::Nil) => Ok(()),

            // Type variable unification
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), ty) | (ty, Type::Var(id)) => {
                // Occurs check: prevent infinite types
                if ty.contains_var(*id) {
                    return Err(TypeError::OccursCheck {
                        var_id: *id,
                        ty: ty.clone(),
                    });
                }
                self.subst.insert(*id, ty.clone());
                Ok(())
            }

            // Named types match by name
            (Type::Named(n1), Type::Named(n2)) if n1 == n2 => Ok(()),

            // Arrays unify if elements unify
            (Type::Array(e1), Type::Array(e2)) => self.unify(e1, e2),

            // Tuples unify if all elements unify
            (Type::Tuple(ts1), Type::Tuple(ts2)) if ts1.len() == ts2.len() => {
                for (a, b) in ts1.iter().zip(ts2.iter()) {
                    self.unify(a, b)?;
                }
                Ok(())
            }

            // Functions unify if params and return types unify
            (
                Type::Function {
                    params: p1,
                    ret: r1,
                },
                Type::Function {
                    params: p2,
                    ret: r2,
                },
            ) if p1.len() == p2.len() => {
                for (a, b) in p1.iter().zip(p2.iter()) {
                    self.unify(a, b)?;
                }
                self.unify(r1, r2)
            }

            // Generic types unify if name and args match
            (Type::Generic { name: n1, args: a1 }, Type::Generic { name: n2, args: a2 })
                if n1 == n2 && a1.len() == a2.len() =>
            {
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }

            // Optional types
            (Type::Optional(i1), Type::Optional(i2)) => self.unify(i1, i2),

            // Dict types
            (Type::Dict { key: k1, value: v1 }, Type::Dict { key: k2, value: v2 }) => {
                self.unify(k1, k2)?;
                self.unify(v1, v2)
            }

            // Type parameters
            (Type::TypeParam(n1), Type::TypeParam(n2)) if n1 == n2 => Ok(()),

            // Union types are compatible if one is a member of the other
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                // Check if other matches any member
                for member in members {
                    if self.types_compatible(other, member) {
                        return Ok(());
                    }
                }
                Err(TypeError::Mismatch {
                    expected: t1.clone(),
                    found: t2.clone(),
                })
            }

            // Borrow types unify if inner types unify
            (Type::Borrow(i1), Type::Borrow(i2)) => self.unify(i1, i2),
            (Type::BorrowMut(i1), Type::BorrowMut(i2)) => self.unify(i1, i2),

            // &mut T can coerce to &T (mutable borrow is subtype of immutable borrow)
            (Type::Borrow(i1), Type::BorrowMut(i2)) => self.unify(i1, i2),

            // Mismatch
            _ => Err(TypeError::Mismatch {
                expected: t1.clone(),
                found: t2.clone(),
            }),
        }
    }

    /// Get the resolved type (applying all substitutions)
    pub fn resolve(&self, ty: &Type) -> Type {
        ty.apply_subst(&self.subst)
    }

    /// Convert an AST type annotation to a type checker Type
    pub fn ast_type_to_type(&mut self, ast_ty: &AstType) -> Type {
        match ast_ty {
            AstType::Simple(name) => {
                // Check if it's a type parameter first
                if let Some(ty) = self.type_params.get(name) {
                    return ty.clone();
                }
                // Map common type names
                match name.as_str() {
                    "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "Int" => {
                        Type::Int
                    }
                    "f32" | "f64" | "float" | "Float" => Type::Float,
                    "bool" | "Bool" => Type::Bool,
                    "str" | "String" | "Str" => Type::Str,
                    "nil" | "Nil" | "None" => Type::Nil,
                    _ => Type::Named(name.clone()),
                }
            }
            AstType::Generic { name, args } => {
                let converted_args: Vec<Type> =
                    args.iter().map(|a| self.ast_type_to_type(a)).collect();
                Type::Generic {
                    name: name.clone(),
                    args: converted_args,
                }
            }
            AstType::Union(types) => {
                let converted: Vec<Type> = types.iter().map(|t| self.ast_type_to_type(t)).collect();
                Type::Union(converted)
            }
            AstType::Tuple(types) => {
                let converted: Vec<Type> = types.iter().map(|t| self.ast_type_to_type(t)).collect();
                Type::Tuple(converted)
            }
            AstType::Array { element, .. } => Type::Array(Box::new(self.ast_type_to_type(element))),
            AstType::Function { params, ret } => {
                let param_types: Vec<Type> =
                    params.iter().map(|p| self.ast_type_to_type(p)).collect();
                let ret_type = ret
                    .as_ref()
                    .map(|r| self.ast_type_to_type(r))
                    .unwrap_or(Type::Nil);
                Type::Function {
                    params: param_types,
                    ret: Box::new(ret_type),
                }
            }
            AstType::Optional(inner) => Type::Optional(Box::new(self.ast_type_to_type(inner))),
            AstType::Pointer { inner, kind } => {
                let inner_type = self.ast_type_to_type(inner);
                match kind {
                    PointerKind::Borrow => Type::Borrow(Box::new(inner_type)),
                    PointerKind::BorrowMut => Type::BorrowMut(Box::new(inner_type)),
                    // For other pointer types, treat as their inner type for now
                    _ => inner_type,
                }
            }
            AstType::Constructor { target, args } => {
                let target_type = self.ast_type_to_type(target);
                let args_types = args
                    .as_ref()
                    .map(|a| a.iter().map(|t| self.ast_type_to_type(t)).collect());
                Type::Constructor {
                    target: Box::new(target_type),
                    args: args_types,
                }
            }
            AstType::Simd { lanes, element } => {
                let elem_type = self.ast_type_to_type(element);
                Type::Simd {
                    lanes: *lanes,
                    element: Box::new(elem_type),
                }
            }
        }
    }

    /// Check if a type is compatible with a union type
    pub fn type_matches_union(&self, ty: &Type, union_members: &[Type]) -> bool {
        for member in union_members {
            if self.types_compatible(ty, member) {
                return true;
            }
        }
        false
    }

    /// Check if two types are compatible (for union type checking)
    pub fn types_compatible(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            // Same primitive types
            (Type::Int, Type::Int) => true,
            (Type::Float, Type::Float) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Str, Type::Str) => true,
            (Type::Nil, Type::Nil) => true,
            // Type variables are compatible with anything
            (Type::Var(_), _) | (_, Type::Var(_)) => true,
            // Named types match by name
            (Type::Named(n1), Type::Named(n2)) => n1 == n2,
            // Arrays match if elements match
            (Type::Array(e1), Type::Array(e2)) => self.types_compatible(e1, e2),
            // Tuples match if all elements match
            (Type::Tuple(t1), Type::Tuple(t2)) => {
                t1.len() == t2.len()
                    && t1
                        .iter()
                        .zip(t2.iter())
                        .all(|(a, b)| self.types_compatible(a, b))
            }
            // Union types: check if either is a subset
            (Type::Union(members), other) | (other, Type::Union(members)) => {
                self.type_matches_union(other, members)
            }
            // Generic types match if name and all args match
            (Type::Generic { name: n1, args: a1 }, Type::Generic { name: n2, args: a2 }) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1
                        .iter()
                        .zip(a2.iter())
                        .all(|(x, y)| self.types_compatible(x, y))
            }
            // Functions match if params and return types match
            (
                Type::Function {
                    params: p1,
                    ret: r1,
                },
                Type::Function {
                    params: p2,
                    ret: r2,
                },
            ) => {
                p1.len() == p2.len()
                    && p1
                        .iter()
                        .zip(p2.iter())
                        .all(|(a, b)| self.types_compatible(a, b))
                    && self.types_compatible(r1, r2)
            }
            // Optional types
            (Type::Optional(inner1), Type::Optional(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            // Dict types
            (Type::Dict { key: k1, value: v1 }, Type::Dict { key: k2, value: v2 }) => {
                self.types_compatible(k1, k2) && self.types_compatible(v1, v2)
            }
            // Type parameters
            (Type::TypeParam(n1), Type::TypeParam(n2)) => n1 == n2,
            // Borrow types
            (Type::Borrow(inner1), Type::Borrow(inner2)) => self.types_compatible(inner1, inner2),
            (Type::BorrowMut(inner1), Type::BorrowMut(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            // &mut T is compatible with &T (mutable borrow can be used where immutable is expected)
            (Type::Borrow(inner1), Type::BorrowMut(inner2)) => {
                self.types_compatible(inner1, inner2)
            }
            _ => false,
        }
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    pub fn check_items(&mut self, items: &[Node]) -> Result<(), TypeError> {
        // Register built-in functions
        let range_ty = self.fresh_var();
        self.env.insert("range".to_string(), range_ty);
        let print_ty = self.fresh_var();
        self.env.insert("print".to_string(), print_ty);
        let len_ty = self.fresh_var();
        self.env.insert("len".to_string(), len_ty);
        let send_ty = self.fresh_var();
        self.env.insert("send".to_string(), send_ty);
        let recv_ty = self.fresh_var();
        self.env.insert("recv".to_string(), recv_ty);
        let reply_ty = self.fresh_var();
        self.env.insert("reply".to_string(), reply_ty);
        let join_ty = self.fresh_var();
        self.env.insert("join".to_string(), join_ty);
        let spawn_ty = self.fresh_var();
        self.env.insert("spawn".to_string(), spawn_ty);
        let spawn_isolated_ty = self.fresh_var();
        self.env.insert("spawn_isolated".to_string(), spawn_isolated_ty);
        // ThreadPool constructor
        let threadpool_ty = self.fresh_var();
        self.env.insert("ThreadPool".to_string(), threadpool_ty);
        // Option type constructors
        let some_ty = self.fresh_var();
        self.env.insert("Some".to_string(), some_ty);
        let none_ty = self.fresh_var();
        self.env.insert("None".to_string(), none_ty);
        // Result type constructors
        let ok_ty = self.fresh_var();
        self.env.insert("Ok".to_string(), ok_ty);
        let err_ty = self.fresh_var();
        self.env.insert("Err".to_string(), err_ty);

        // First pass: register all function, class, struct, const, static names
        for item in items {
            match item {
                Node::Function(func) => {
                    let ty = self.fresh_var();
                    self.env.insert(func.name.clone(), ty);
                }
                Node::Class(class) => {
                    let ty = self.fresh_var();
                    self.env.insert(class.name.clone(), ty);
                }
                Node::Struct(s) => {
                    let ty = self.fresh_var();
                    self.env.insert(s.name.clone(), ty);
                }
                Node::Enum(e) => {
                    let ty = self.fresh_var();
                    self.env.insert(e.name.clone(), ty);
                }
                Node::Trait(t) => {
                    // Register trait as a type for now
                    let ty = self.fresh_var();
                    self.env.insert(t.name.clone(), ty);
                }
                Node::Const(c) => {
                    let ty = self.fresh_var();
                    self.env.insert(c.name.clone(), ty);
                }
                Node::Static(s) => {
                    let ty = self.fresh_var();
                    self.env.insert(s.name.clone(), ty);
                }
                Node::Extern(ext) => {
                    let ty = self.fresh_var();
                    self.env.insert(ext.name.clone(), ty);
                }
                Node::Macro(m) => {
                    // Register macro as a special type (macros are compile-time)
                    let ty = self.fresh_var();
                    self.env.insert(m.name.clone(), ty);
                }
                Node::Actor(a) => {
                    // Register actor as a type
                    let ty = self.fresh_var();
                    self.env.insert(a.name.clone(), ty);
                }
                Node::TypeAlias(t) => {
                    // Register type alias
                    let ty = self.fresh_var();
                    self.env.insert(t.name.clone(), ty);
                }
                Node::Unit(u) => {
                    // Register unit type
                    let ty = self.fresh_var();
                    self.env.insert(u.name.clone(), ty);
                }
                Node::UnitFamily(uf) => {
                    // Register unit family type
                    let ty = self.fresh_var();
                    self.env.insert(uf.name.clone(), ty);
                }
                Node::Impl(_) => {
                    // Impl blocks don't introduce new names
                }
                Node::Let(_)
                | Node::Assignment(_)
                | Node::Return(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::Break(_)
                | Node::Continue(_)
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {
                    // Statement nodes at module level are checked in second pass
                }
                // Module system nodes (parsed but not type-checked at this level)
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::AutoImportStmt(_) => {
                    // Module system nodes don't introduce type bindings directly
                }
            }
        }
        // Second pass: check all nodes
        for item in items {
            self.check_node(item)?;
        }
        Ok(())
    }

    fn check_node(&mut self, node: &Node) -> Result<(), TypeError> {
        match node {
            Node::Let(let_stmt) => {
                if let Some(expr) = &let_stmt.value {
                    let _ty = self.infer_expr(expr)?;
                    // Bind all identifiers in the pattern
                    self.bind_pattern(&let_stmt.pattern);
                }
                Ok(())
            }
            Node::Const(const_stmt) => {
                let ty = self.infer_expr(&const_stmt.value)?;
                self.env.insert(const_stmt.name.clone(), ty);
                Ok(())
            }
            Node::Static(static_stmt) => {
                let ty = self.infer_expr(&static_stmt.value)?;
                self.env.insert(static_stmt.name.clone(), ty);
                Ok(())
            }
            Node::Assignment(assign) => {
                let ty = self.infer_expr(&assign.value)?;
                // Python-like: assignment can create new variables
                if let Expr::Identifier(name) = &assign.target {
                    self.env.insert(name.clone(), ty);
                }
                Ok(())
            }
            Node::Function(func) => {
                // Register the function name in current scope (for nested functions)
                let func_ty = self.fresh_var();
                self.env.insert(func.name.clone(), func_ty.clone());

                let old_env = self.env.clone();
                for param in &func.params {
                    // Use type annotation if present, otherwise create fresh var
                    let ty = if let Some(ref ast_ty) = param.ty {
                        self.ast_type_to_type(ast_ty)
                    } else {
                        self.fresh_var()
                    };
                    self.env.insert(param.name.clone(), ty);
                }
                for stmt in &func.body.statements {
                    self.check_node(stmt)?;
                }
                self.env = old_env;
                // Re-add function name after restoring env (it was added before saving old_env)
                self.env.insert(func.name.clone(), func_ty);
                Ok(())
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(())
            }
            Node::Expression(expr) => {
                let _ = self.infer_expr(expr)?;
                Ok(())
            }
            Node::If(if_stmt) => {
                let _ = self.infer_expr(&if_stmt.condition)?;
                // Handle if let pattern binding
                if let Some(pattern) = &if_stmt.let_pattern {
                    self.bind_pattern(pattern);
                }
                for stmt in &if_stmt.then_block.statements {
                    self.check_node(stmt)?;
                }
                for (cond, block) in &if_stmt.elif_branches {
                    let _ = self.infer_expr(cond)?;
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                if let Some(block) = &if_stmt.else_block {
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(())
            }
            Node::While(while_stmt) => {
                let _ = self.infer_expr(&while_stmt.condition)?;
                // Handle while let pattern binding
                if let Some(pattern) = &while_stmt.let_pattern {
                    self.bind_pattern(pattern);
                }
                for stmt in &while_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::For(for_stmt) => {
                let _ = self.infer_expr(&for_stmt.iterable)?;
                if let Pattern::Identifier(name) = &for_stmt.pattern {
                    let ty = self.fresh_var();
                    self.env.insert(name.clone(), ty);
                }
                for stmt in &for_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::Loop(loop_stmt) => {
                for stmt in &loop_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::Context(ctx_stmt) => {
                // Check the context expression
                let _ = self.infer_expr(&ctx_stmt.context)?;
                // Check body statements - note: in context blocks, unknown methods
                // are dispatched to the context object, so we allow more flexibility
                for stmt in &ctx_stmt.body.statements {
                    // Be lenient with type checking inside context blocks
                    let _ = self.check_node(stmt);
                }
                Ok(())
            }
            Node::Match(match_stmt) => {
                let _ = self.infer_expr(&match_stmt.subject)?;
                for arm in &match_stmt.arms {
                    self.bind_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        let _ = self.infer_expr(guard)?;
                    }
                    for stmt in &arm.body.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(())
            }
            Node::Trait(trait_def) => {
                // Check all trait methods
                for method in &trait_def.methods {
                    let old_env = self.env.clone();
                    for param in &method.params {
                        let ty = self.fresh_var();
                        self.env.insert(param.name.clone(), ty);
                    }
                    for stmt in &method.body.statements {
                        self.check_node(stmt)?;
                    }
                    self.env = old_env;
                }
                Ok(())
            }
            Node::Impl(impl_block) => {
                // Check all impl methods
                for method in &impl_block.methods {
                    let old_env = self.env.clone();
                    // Add self to environment
                    let self_ty = self.fresh_var();
                    self.env.insert("self".to_string(), self_ty);
                    for param in &method.params {
                        if param.name != "self" {
                            let ty = self.fresh_var();
                            self.env.insert(param.name.clone(), ty);
                        }
                    }
                    for stmt in &method.body.statements {
                        self.check_node(stmt)?;
                    }
                    self.env = old_env;
                }
                Ok(())
            }
            Node::With(with_stmt) => {
                // Check the resource expression
                let _ = self.infer_expr(&with_stmt.resource)?;
                // Bind the "as name" if present
                if let Some(name) = &with_stmt.name {
                    let ty = self.fresh_var();
                    self.env.insert(name.clone(), ty);
                }
                // Check body statements
                for stmt in &with_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Identifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::MutIdentifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::Tuple(patterns) | Pattern::Array(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Struct { fields, .. } => {
                for (_, p) in fields {
                    self.bind_pattern(p);
                }
            }
            Pattern::Enum { payload, .. } => {
                if let Some(patterns) = payload {
                    for p in patterns {
                        self.bind_pattern(p);
                    }
                }
            }
            Pattern::Or(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Typed { pattern, .. } => {
                self.bind_pattern(pattern);
            }
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Rest | Pattern::Range { .. } => {
                // These patterns don't bind any names
            }
        }
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Integer(_) => Ok(Type::Int),
            Expr::Float(_) => Ok(Type::Float),
            Expr::String(_) => Ok(Type::Str),
            Expr::FString(parts) => {
                use simple_parser::ast::FStringPart;
                for part in parts {
                    if let FStringPart::Expr(e) = part {
                        let _ = self.infer_expr(e)?;
                    }
                }
                Ok(Type::Str)
            }
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Nil => Ok(Type::Nil),
            Expr::Identifier(name) => self
                .env
                .get(name)
                .cloned()
                .ok_or_else(|| TypeError::Undefined(format!("undefined identifier: {}", name))),
            Expr::Binary { left, right, op } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;

                match op {
                    // Arithmetic operators: both operands should be numeric, result is numeric
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::Pow
                    | BinOp::FloorDiv => {
                        // Unify operands to ensure they're compatible
                        let _ = self.unify(&left_ty, &right_ty);
                        Ok(self.resolve(&left_ty))
                    }
                    // Comparison operators: result is always Bool
                    BinOp::Eq
                    | BinOp::NotEq
                    | BinOp::Lt
                    | BinOp::LtEq
                    | BinOp::Gt
                    | BinOp::GtEq => {
                        // Operands should be comparable (same type)
                        let _ = self.unify(&left_ty, &right_ty);
                        Ok(Type::Bool)
                    }
                    // Logical operators: both operands should be Bool, result is Bool
                    BinOp::And | BinOp::Or => {
                        let _ = self.unify(&left_ty, &Type::Bool);
                        let _ = self.unify(&right_ty, &Type::Bool);
                        Ok(Type::Bool)
                    }
                    // Bitwise operators: both operands should be Int
                    BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::BitXor
                    | BinOp::ShiftLeft
                    | BinOp::ShiftRight => {
                        let _ = self.unify(&left_ty, &Type::Int);
                        let _ = self.unify(&right_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                    // Is and In operators
                    BinOp::Is | BinOp::In => Ok(Type::Bool),
                }
            }
            Expr::Unary { op, operand } => {
                use simple_parser::ast::UnaryOp;
                let operand_ty = self.infer_expr(operand)?;
                match op {
                    UnaryOp::Ref => Ok(Type::Borrow(Box::new(operand_ty))),
                    UnaryOp::RefMut => Ok(Type::BorrowMut(Box::new(operand_ty))),
                    UnaryOp::Deref => {
                        // Dereferencing a borrow gives the inner type
                        match operand_ty {
                            Type::Borrow(inner) | Type::BorrowMut(inner) => Ok(*inner),
                            _ => Ok(operand_ty), // For other types, just pass through
                        }
                    }
                    UnaryOp::Neg => {
                        let _ = self.unify(&operand_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                    UnaryOp::Not => Ok(Type::Bool),
                    UnaryOp::BitNot => {
                        let _ = self.unify(&operand_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                }
            }
            Expr::Call { callee, args } => {
                let callee_ty = self.infer_expr(callee)?;
                let mut arg_types = Vec::new();
                for arg in args {
                    arg_types.push(self.infer_expr(&arg.value)?);
                }
                // If callee has a function type, use its return type
                let result_ty = self.fresh_var();
                match self.resolve(&callee_ty) {
                    Type::Function { params, ret } => {
                        // Unify argument types with parameter types
                        for (arg_ty, param_ty) in arg_types.iter().zip(params.iter()) {
                            let _ = self.unify(arg_ty, param_ty);
                        }
                        Ok(*ret)
                    }
                    _ => Ok(result_ty),
                }
            }
            Expr::Array(items) => {
                if items.is_empty() {
                    // Empty array has unknown element type
                    let elem_ty = self.fresh_var();
                    Ok(Type::Array(Box::new(elem_ty)))
                } else {
                    // Infer element type from first item, unify with rest
                    let first_ty = self.infer_expr(&items[0])?;
                    for item in items.iter().skip(1) {
                        let item_ty = self.infer_expr(item)?;
                        let _ = self.unify(&first_ty, &item_ty);
                    }
                    Ok(Type::Array(Box::new(self.resolve(&first_ty))))
                }
            }
            Expr::Index { receiver, index } => {
                let recv_ty = self.infer_expr(receiver)?;
                let idx_ty = self.infer_expr(index)?;
                // Index should be Int for arrays
                let _ = self.unify(&idx_ty, &Type::Int);
                // Result type depends on receiver
                match self.resolve(&recv_ty) {
                    Type::Array(elem) => Ok(*elem),
                    Type::Str => Ok(Type::Str), // String indexing returns string/char
                    Type::Dict { value, .. } => Ok(*value),
                    Type::Tuple(_types) => {
                        // Tuple indexing - type depends on index literal
                        // For now, return fresh var since we don't know which element
                        Ok(self.fresh_var())
                    }
                    _ => Ok(self.fresh_var()),
                }
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(condition)?;
                // Condition should be Bool
                let _ = self.unify(&cond_ty, &Type::Bool);
                let then_ty = self.infer_expr(then_branch)?;
                if let Some(else_b) = else_branch {
                    let else_ty = self.infer_expr(else_b)?;
                    // Both branches should have same type
                    let _ = self.unify(&then_ty, &else_ty);
                }
                Ok(self.resolve(&then_ty))
            }
            Expr::Match { subject, arms } => {
                let _ = self.infer_expr(subject)?;
                let result_ty = self.fresh_var();
                for arm in arms {
                    self.bind_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        let _ = self.infer_expr(guard)?;
                    }
                    for stmt in &arm.body.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(result_ty)
            }
            Expr::FieldAccess { receiver, .. } => {
                let _ = self.infer_expr(receiver)?;
                Ok(self.fresh_var())
            }
            Expr::MethodCall { receiver, args, .. } => {
                let _ = self.infer_expr(receiver)?;
                for arg in args {
                    let _ = self.infer_expr(&arg.value)?;
                }
                Ok(self.fresh_var())
            }
            Expr::StructInit { fields, .. } => {
                for (_, expr) in fields {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Path(_) => Ok(self.fresh_var()),
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    let _ = self.infer_expr(s)?;
                }
                if let Some(e) = end {
                    let _ = self.infer_expr(e)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Dict(entries) => {
                for (k, v) in entries {
                    let _ = self.infer_expr(k)?;
                    let _ = self.infer_expr(v)?;
                }
                Ok(self.fresh_var())
            }
            _ => Ok(self.fresh_var()),
        }
    }
}

/// Check a list of AST nodes for type errors
pub fn check(items: &[Node]) -> Result<(), TypeError> {
    let mut checker = TypeChecker::new();
    checker.check_items(items)
}
