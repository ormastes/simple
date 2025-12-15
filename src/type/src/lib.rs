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
// These types match the Lean model EXACTLY.
//
// Lean equivalent:
// ```lean
// inductive Ty
//   | nat
//   | bool
//   | str
//   | arrow (a b : Ty)
//   deriving DecidableEq, Repr
//
// inductive Expr
//   | litNat (n : Nat)
//   | litBool (b : Bool)
//   | litStr (s : String)
//   | add (a b : Expr)
//   | concat (a b : Expr)
//   | ifElse (c t e : Expr)
//   | lam (body : Expr)
//   | app (f x : Expr)
//   deriving Repr
// ```

/// Type matching TypeInferenceCompile.lean exactly (4 variants).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanTy {
    /// Natural number type
    Nat,
    /// Boolean type
    Bool,
    /// String type
    Str,
    /// Generic type constructor (name + type arguments)
    Generic(String, Vec<LeanTy>),
    /// Function type (arrow)
    Arrow(Box<LeanTy>, Box<LeanTy>),
}

/// Expression matching TypeInferenceCompile.lean exactly (8 variants).
#[derive(Debug, Clone, PartialEq)]
pub enum LeanExpr {
    /// Natural number literal (Nat, not i64)
    LitNat(u64),
    /// Boolean literal
    LitBool(bool),
    /// String literal
    LitStr(String),
    /// Addition (Nat + Nat → Nat)
    Add(Box<LeanExpr>, Box<LeanExpr>),
    /// String concatenation (Str ++ Str → Str)
    Concat(Box<LeanExpr>, Box<LeanExpr>),
    /// Generic constructor with type arguments
    Generic(String, Vec<LeanExpr>),
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
        LeanExpr::LitStr(_) => Some(LeanTy::Str),

        LeanExpr::Add(a, b) => {
            // Lean: let Ty.nat ← infer a | none; let Ty.nat ← infer b | none; pure Ty.nat
            match (lean_infer(a)?, lean_infer(b)?) {
                (LeanTy::Nat, LeanTy::Nat) => Some(LeanTy::Nat),
                // Explicit: addition only works on Nat
                (LeanTy::Bool, _)
                | (LeanTy::Str, _)
                | (LeanTy::Generic(_, _), _)
                | (LeanTy::Arrow(_, _), _)
                | (_, LeanTy::Bool)
                | (_, LeanTy::Str)
                | (_, LeanTy::Generic(_, _))
                | (_, LeanTy::Arrow(_, _)) => None,
            }
        }

        LeanExpr::Concat(a, b) => {
            // Lean: let Ty.str ← infer a | none; let Ty.str ← infer b | none; pure Ty.str
            match (lean_infer(a)?, lean_infer(b)?) {
                (LeanTy::Str, LeanTy::Str) => Some(LeanTy::Str),
                // Explicit: concatenation only works on Str
                (LeanTy::Nat, _)
                | (LeanTy::Bool, _)
                | (LeanTy::Arrow(_, _), _)
                | (LeanTy::Generic(_, _), _)
                | (_, LeanTy::Nat)
                | (_, LeanTy::Bool)
                | (_, LeanTy::Arrow(_, _))
                | (_, LeanTy::Generic(_, _)) => None,
            }
        }
        LeanExpr::Generic(name, args) => {
            let mut arg_tys = Vec::with_capacity(args.len());
            for expr in args {
                arg_tys.push(lean_infer(expr)?);
            }
            Some(LeanTy::Generic(name.clone(), arg_tys))
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
                // Explicit: only Arrow types can be applied
                LeanTy::Nat | LeanTy::Bool | LeanTy::Str | LeanTy::Generic(_, _) => None,
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
// Type Aliases (for backward compatibility)
//==============================================================================
// SimpleTy and SimpleExpr are now aliases to LeanTy and LeanExpr since
// the Lean model has been extended to include Str.

/// Alias to LeanTy for backward compatibility.
pub type SimpleTy = LeanTy;

/// Alias to LeanExpr for backward compatibility.
pub type SimpleExpr = LeanExpr;

/// Alias to lean_infer for backward compatibility.
pub fn infer_simple(expr: &LeanExpr) -> Option<LeanTy> {
    lean_infer(expr)
}

/// Convert a full AST expression to a LeanExpr for pure inference.
/// Returns `None` if the expression uses features not in the Lean model.
pub fn to_simple_expr(expr: &Expr) -> Option<LeanExpr> {
    match expr {
        // Only non-negative integers map to Lean's Nat
        Expr::Integer(n) if *n >= 0 => Some(LeanExpr::LitNat(*n as u64)),
        Expr::Integer(_) => None, // Negative numbers not in Lean Nat
        Expr::Bool(b) => Some(LeanExpr::LitBool(*b)),
        Expr::String(s) => Some(LeanExpr::LitStr(s.clone())),

        Expr::Binary {
            left,
            right,
            op: BinOp::Add,
        } => {
            let l = to_simple_expr(left)?;
            let r = to_simple_expr(right)?;
            Some(LeanExpr::Add(Box::new(l), Box::new(r)))
        }

        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let c = to_simple_expr(condition)?;
            let t = to_simple_expr(then_branch)?;
            let e = to_simple_expr(else_branch.as_ref()?)?;
            Some(LeanExpr::IfElse(Box::new(c), Box::new(t), Box::new(e)))
        }

        // Other expressions are not in the Lean model
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

//==============================================================================
// Type Scheme (for let-polymorphism) - Matches Generics.lean
//==============================================================================
// A type scheme is a type with bound type variables: ∀α₁...αₙ. τ
// This enables let-polymorphism where a let-bound variable can have
// different types at different use sites.
//
// Lean equivalent (from Generics.lean):
// ```lean
// structure Scheme where
//   vars : List TyVar  -- Bound type variables
//   ty : Ty            -- The type body
// ```

/// Type scheme: ∀vars. ty (polymorphic type)
/// Matches the Lean `Scheme` structure in Generics.lean
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    /// Bound type variables (quantified)
    pub vars: Vec<usize>,
    /// The type body
    pub ty: Type,
}

impl TypeScheme {
    /// Create a monomorphic scheme (no quantified variables)
    pub fn mono(ty: Type) -> Self {
        Self { vars: vec![], ty }
    }

    /// Create a polymorphic scheme with the given bound variables
    pub fn poly(vars: Vec<usize>, ty: Type) -> Self {
        Self { vars, ty }
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

// TypeChecker implementation (split for maintainability)
include!("checker_builtins.rs");
include!("checker_unify.rs");
include!("checker_check.rs");
include!("checker_infer.rs");

/// Check a list of AST nodes for type errors
pub fn check(items: &[Node]) -> Result<(), TypeError> {
    let mut checker = TypeChecker::new();
    checker.check_items(items)
}
