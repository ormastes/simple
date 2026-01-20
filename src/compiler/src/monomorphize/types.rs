//! Type definitions for monomorphization.

use simple_parser::ast::ReferenceCapability;
use std::collections::HashMap;

/// A unique key for a specialization.
///
/// Combines the original name with the concrete type arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpecializationKey {
    /// Original generic function/struct name
    pub name: String,
    /// Concrete type arguments (e.g., [Int, String])
    pub type_args: Vec<ConcreteType>,
}

impl SpecializationKey {
    pub fn new(name: impl Into<String>, type_args: Vec<ConcreteType>) -> Self {
        Self {
            name: name.into(),
            type_args,
        }
    }

    /// Generate a mangled name for the specialization.
    ///
    /// Example: `identity` with `[Int]` -> `identity$Int`
    pub fn mangled_name(&self) -> String {
        if self.type_args.is_empty() {
            self.name.clone()
        } else {
            let args_str = self
                .type_args
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join("_");
            format!("{}${}", self.name, args_str)
        }
    }
}

/// A concrete (non-generic) type.
///
/// This represents types after type parameters have been substituted.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConcreteType {
    /// Primitive types
    Int,
    Float,
    Bool,
    String,
    Nil,

    /// Named type (struct, class, enum)
    Named(String),

    /// Array of element type
    Array(Box<ConcreteType>),

    /// Tuple of types
    Tuple(Vec<ConcreteType>),

    /// Dictionary
    Dict {
        key: Box<ConcreteType>,
        value: Box<ConcreteType>,
    },

    /// Function type
    Function {
        params: Vec<ConcreteType>,
        ret: Box<ConcreteType>,
    },

    /// Optional type
    Optional(Box<ConcreteType>),

    /// Pointer types
    Pointer {
        kind: PointerKind,
        capability: ReferenceCapability,
        inner: Box<ConcreteType>,
    },

    /// Specialized generic (after substitution)
    /// e.g., List[Int] becomes Specialized { name: "List", args: [Int] }
    Specialized {
        name: String,
        args: Vec<ConcreteType>,
    },
}

/// Pointer kinds for memory management.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PointerKind {
    Unique,
    Shared,
    Weak,
    Handle,
    Borrow,
    BorrowMut,
    RawConst,
    RawMut,
}

impl std::fmt::Display for ConcreteType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcreteType::Int => write!(f, "Int"),
            ConcreteType::Float => write!(f, "Float"),
            ConcreteType::Bool => write!(f, "Bool"),
            ConcreteType::String => write!(f, "String"),
            ConcreteType::Nil => write!(f, "Nil"),
            ConcreteType::Named(name) => write!(f, "{}", name),
            ConcreteType::Array(elem) => write!(f, "Array_{}", elem),
            ConcreteType::Tuple(elems) => {
                let s = elems.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("_");
                write!(f, "Tuple_{}", s)
            }
            ConcreteType::Dict { key, value } => write!(f, "Dict_{}_{}", key, value),
            ConcreteType::Function { params, ret } => {
                let p = params.iter().map(|p| p.to_string()).collect::<Vec<_>>().join("_");
                write!(f, "Fn_{}_{}", p, ret)
            }
            ConcreteType::Optional(inner) => write!(f, "Opt_{}", inner),
            ConcreteType::Pointer { kind, capability, inner } => {
                let k = match kind {
                    PointerKind::Unique => "Unique",
                    PointerKind::Shared => "Shared",
                    PointerKind::Weak => "Weak",
                    PointerKind::Handle => "Handle",
                    PointerKind::Borrow => "Borrow",
                    PointerKind::BorrowMut => "BorrowMut",
                    PointerKind::RawConst => "RawConst",
                    PointerKind::RawMut => "RawMut",
                };
                let cap = match capability {
                    ReferenceCapability::Shared => "sh",
                    ReferenceCapability::Exclusive => "ex",
                    ReferenceCapability::Isolated => "iso",
                };
                write!(f, "{}{}_{}", k, cap, inner)
            }
            ConcreteType::Specialized { name, args } => {
                let a = args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join("_");
                write!(f, "{}_{}", name, a)
            }
        }
    }
}

/// Type bindings: maps type parameter names to concrete types.
pub type TypeBindings = HashMap<String, ConcreteType>;
