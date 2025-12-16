//! Utility functions for type conversion.

use super::types::{ConcreteType, PointerKind};
use simple_parser::ast::{Expr, Type as AstType};
use std::collections::HashMap;

#[cfg(test)]
use super::rewriter::monomorphize_module;
#[cfg(test)]
use super::table::MonomorphizationTable;
#[cfg(test)]
use super::types::SpecializationKey;
#[cfg(test)]
use simple_parser::ast::{Block, FunctionDef, Node};
#[cfg(test)]
use simple_parser::Span;

/// Check if a type directly uses a type parameter.
pub fn type_uses_param(ty: &AstType, param: &str) -> bool {
    match ty {
        AstType::Simple(name) => name == param,
        AstType::Generic { name, args } => {
            name == param || args.iter().any(|a| type_uses_param(a, param))
        }
        AstType::Array { element, .. } => type_uses_param(element, param),
        AstType::Tuple(elems) => elems.iter().any(|e| type_uses_param(e, param)),
        AstType::Function { params, ret } => {
            params.iter().any(|p| type_uses_param(p, param))
                || ret
                    .as_ref()
                    .map_or(false, |r| type_uses_param(r, param))
        }
        AstType::Optional(inner) => type_uses_param(inner, param),
        AstType::Pointer { inner, .. } => type_uses_param(inner, param),
        _ => false,
    }
}

/// Infer the concrete type of an expression.
pub fn infer_concrete_type(expr: &Expr, type_context: &HashMap<String, ConcreteType>) -> Option<ConcreteType> {
    match expr {
        Expr::Integer(_) | Expr::TypedInteger(_, _) => Some(ConcreteType::Int),
        Expr::Float(_) | Expr::TypedFloat(_, _) => Some(ConcreteType::Float),
        Expr::Bool(_) => Some(ConcreteType::Bool),
        Expr::String(_) | Expr::TypedString(_, _) | Expr::FString(_) => {
            Some(ConcreteType::String)
        }
        Expr::Nil => Some(ConcreteType::Nil),
        Expr::Identifier(name) => type_context.get(name).cloned(),
        Expr::Array(elems) => {
            if let Some(first) = elems.first() {
                Some(ConcreteType::Array(Box::new(
                    infer_concrete_type(first, type_context)?,
                )))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub fn ast_type_to_concrete(
    ty: &AstType,
    bindings: &HashMap<String, ConcreteType>,
) -> ConcreteType {
    match ty {
        AstType::Simple(name) => {
            // Check if it's a type parameter
            if let Some(concrete) = bindings.get(name) {
                return concrete.clone();
            }

            // Check for primitive types
            match name.as_str() {
                "Int" | "i32" | "i64" | "i8" | "i16" => ConcreteType::Int,
                "Float" | "f32" | "f64" => ConcreteType::Float,
                "Bool" | "bool" => ConcreteType::Bool,
                "String" | "str" => ConcreteType::String,
                "Nil" | "nil" | "()" => ConcreteType::Nil,
                _ => ConcreteType::Named(name.clone()),
            }
        }
        AstType::Generic { name, args } => {
            // Check if the name itself is a type parameter
            if let Some(concrete) = bindings.get(name) {
                return concrete.clone();
            }

            let concrete_args: Vec<ConcreteType> = args
                .iter()
                .map(|a| ast_type_to_concrete(a, bindings))
                .collect();

            ConcreteType::Specialized {
                name: name.clone(),
                args: concrete_args,
            }
        }
        AstType::Tuple(elems) => ConcreteType::Tuple(
            elems
                .iter()
                .map(|e| ast_type_to_concrete(e, bindings))
                .collect(),
        ),
        AstType::Array { element, size: _ } => {
            ConcreteType::Array(Box::new(ast_type_to_concrete(element, bindings)))
        }
        AstType::Function { params, ret } => ConcreteType::Function {
            params: params
                .iter()
                .map(|p| ast_type_to_concrete(p, bindings))
                .collect(),
            ret: Box::new(
                ret.as_ref()
                    .map(|r| ast_type_to_concrete(r, bindings))
                    .unwrap_or(ConcreteType::Nil),
            ),
        },
        AstType::Optional(inner) => {
            ConcreteType::Optional(Box::new(ast_type_to_concrete(inner, bindings)))
        }
        AstType::Pointer { kind, inner } => {
            let pk = match kind {
                simple_parser::ast::PointerKind::Unique => PointerKind::Unique,
                simple_parser::ast::PointerKind::Shared => PointerKind::Shared,
                simple_parser::ast::PointerKind::Weak => PointerKind::Weak,
                simple_parser::ast::PointerKind::Handle => PointerKind::Handle,
                simple_parser::ast::PointerKind::Borrow => PointerKind::Borrow,
                simple_parser::ast::PointerKind::BorrowMut => PointerKind::BorrowMut,
            };
            ConcreteType::Pointer {
                kind: pk,
                inner: Box::new(ast_type_to_concrete(inner, bindings)),
            }
        }
        AstType::Union(types) => {
            // For unions, we take the first type for now
            // A more complete implementation would create a union concrete type
            if let Some(first) = types.first() {
                ast_type_to_concrete(first, bindings)
            } else {
                ConcreteType::Nil
            }
        }
        AstType::Constructor { target, args: _ } => {
            // Constructor types are used for factory patterns
            // We extract the target type
            ast_type_to_concrete(target, bindings)
        }
        AstType::Simd { lanes: _, element } => {
            // SIMD types are specialized arrays
            ConcreteType::Array(Box::new(ast_type_to_concrete(element, bindings)))
        }
        AstType::DynTrait(trait_name) => {
            // dyn Trait - represents a trait object (fat pointer)
            ConcreteType::Named(format!("dyn_{}", trait_name))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_specialization_key() {
        let key = SpecializationKey::new("identity", vec![ConcreteType::Int]);
        assert_eq!(key.mangled_name(), "identity$Int");

        let key2 = SpecializationKey::new("swap", vec![ConcreteType::Int, ConcreteType::String]);
        assert_eq!(key2.mangled_name(), "swap$Int_String");
    }

    #[test]
    fn test_concrete_type_display() {
        assert_eq!(ConcreteType::Int.to_string(), "Int");
        assert_eq!(
            ConcreteType::Array(Box::new(ConcreteType::Int)).to_string(),
            "Array_Int"
        );
        assert_eq!(
            ConcreteType::Specialized {
                name: "List".to_string(),
                args: vec![ConcreteType::String],
            }
            .to_string(),
            "List_String"
        );
    }

    #[test]
    fn test_monomorphization_table() {
        let mut table = MonomorphizationTable::new();

        let func = FunctionDef {
            span: Span::new(0, 0, 1, 1),
            name: "identity".to_string(),
            generic_params: vec!["T".to_string()],
            where_clause: vec![],
            params: vec![],
            return_type: None,
            body: Block {
                span: Span::new(0, 0, 1, 1),
                statements: vec![],
            },
            visibility: simple_parser::ast::Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
        };

        let mangled = table.request_function("identity", vec![ConcreteType::Int], &func);
        assert_eq!(mangled, "identity$Int");
        assert!(table.has_pending());

        let (key, _) = table.pop_pending_function().unwrap();
        assert_eq!(key.name, "identity");
        assert!(!table.has_pending());
    }

    #[test]
    fn test_ast_type_to_concrete() {
        let bindings: HashMap<String, ConcreteType> = HashMap::new();

        let int_ty = AstType::Simple("Int".to_string());
        assert_eq!(ast_type_to_concrete(&int_ty, &bindings), ConcreteType::Int);

        let array_ty = AstType::Array {
            element: Box::new(AstType::Simple("String".to_string())),
            size: None,
        };
        assert_eq!(
            ast_type_to_concrete(&array_ty, &bindings),
            ConcreteType::Array(Box::new(ConcreteType::String))
        );
    }

    #[test]
    fn test_type_parameter_substitution() {
        let mut bindings = HashMap::new();
        bindings.insert("T".to_string(), ConcreteType::Int);

        let param_ty = AstType::Simple("T".to_string());
        assert_eq!(
            ast_type_to_concrete(&param_ty, &bindings),
            ConcreteType::Int
        );

        let generic_ty = AstType::Generic {
            name: "List".to_string(),
            args: vec![AstType::Simple("T".to_string())],
        };
        assert_eq!(
            ast_type_to_concrete(&generic_ty, &bindings),
            ConcreteType::Specialized {
                name: "List".to_string(),
                args: vec![ConcreteType::Int],
            }
        );
    }

    #[test]
    fn test_monomorphize_identity_function() {
        let code = r#"
fn identity<T>(x: T) -> T:
    return x

main = identity(42)
"#;
        let mut parser = simple_parser::Parser::new(code);
        let module = parser.parse().expect("parse ok");
        let mono_module = monomorphize_module(&module);

        // Verify we have the specialized function
        let has_specialized = mono_module
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(f) if f.name == "identity$Int"));
        assert!(has_specialized, "Should have identity$Int function");

        // Check that generic identity was removed
        let has_generic = mono_module.items.iter().any(|item| {
            matches!(item, Node::Function(f) if f.name == "identity" && !f.generic_params.is_empty())
        });
        assert!(!has_generic, "Generic identity function should be removed");

        // Check that the call site was rewritten
        let call_rewritten = mono_module.items.iter().any(|item| {
            if let Node::Assignment(a) = item {
                if let Expr::Call { callee, .. } = &a.value {
                    return matches!(callee.as_ref(), Expr::Identifier(name) if name == "identity$Int");
                }
            }
            false
        });
        assert!(
            call_rewritten,
            "Call site should be rewritten to identity$Int"
        );
    }
}

/// Convert a ConcreteType to an AST Type.
pub fn concrete_to_ast_type(concrete: &ConcreteType) -> AstType {
    match concrete {
        ConcreteType::Int => AstType::Simple("Int".to_string()),
        ConcreteType::Float => AstType::Simple("Float".to_string()),
        ConcreteType::Bool => AstType::Simple("Bool".to_string()),
        ConcreteType::String => AstType::Simple("String".to_string()),
        ConcreteType::Nil => AstType::Simple("Nil".to_string()),
        ConcreteType::Named(name) => AstType::Simple(name.clone()),
        ConcreteType::Array(elem) => AstType::Array {
            element: Box::new(concrete_to_ast_type(elem)),
            size: None,
        },
        ConcreteType::Tuple(elems) => {
            AstType::Tuple(elems.iter().map(concrete_to_ast_type).collect())
        }
        ConcreteType::Dict { key, value } => {
            AstType::Generic {
                name: "Dict".to_string(),
                args: vec![concrete_to_ast_type(key), concrete_to_ast_type(value)],
            }
        }
        ConcreteType::Function { params, ret } => AstType::Function {
            params: params.iter().map(concrete_to_ast_type).collect(),
            ret: Some(Box::new(concrete_to_ast_type(ret))),
        },
        ConcreteType::Optional(inner) => AstType::Optional(Box::new(concrete_to_ast_type(inner))),
        ConcreteType::Pointer { kind, inner } => {
            let ast_kind = match kind {
                PointerKind::Unique => simple_parser::ast::PointerKind::Unique,
                PointerKind::Shared => simple_parser::ast::PointerKind::Shared,
                PointerKind::Weak => simple_parser::ast::PointerKind::Weak,
                PointerKind::Handle => simple_parser::ast::PointerKind::Handle,
                PointerKind::Borrow => simple_parser::ast::PointerKind::Borrow,
                PointerKind::BorrowMut => simple_parser::ast::PointerKind::BorrowMut,
            };
            AstType::Pointer {
                kind: ast_kind,
                inner: Box::new(concrete_to_ast_type(inner)),
            }
        }
        ConcreteType::Specialized { name, args: _ } => {
            AstType::Simple(name.clone())
        }
    }
}
