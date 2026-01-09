// HIR types module - split from monolithic types.rs

use std::collections::HashMap;

// Module declarations
pub mod aop;
pub mod code_layout;
pub mod contracts;
pub mod expressions;
pub mod functions;
pub mod layout;
pub mod layout_config;
pub mod module;
pub mod statements;
pub mod type_system;
pub mod verification;

// GPU intrinsics
/// GPU intrinsic function kind for kernel-side operations
include!("../gpu_intrinsics.rs");

// Type registry
include!("../type_registry.rs");

// Re-export all public types
pub use aop::*;
pub use code_layout::*;
pub use contracts::*;
pub use expressions::*;
pub use functions::*;
pub use layout::*;
pub use layout_config::*;
pub use module::*;
pub use statements::*;
pub use type_system::*;
pub use verification::*;

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::{Mutability, Visibility};

    #[test]
    fn test_type_registry_builtins() {
        let registry = TypeRegistry::new();

        assert_eq!(registry.get(TypeId::VOID), Some(&HirType::Void));
        assert_eq!(registry.get(TypeId::BOOL), Some(&HirType::Bool));
        assert_eq!(registry.get(TypeId::I64), Some(&HirType::signed_int(64)));
        assert_eq!(
            registry.get(TypeId::F64),
            Some(&HirType::Float { bits: 64 })
        );
        assert_eq!(registry.get(TypeId::STRING), Some(&HirType::String));
    }

    #[test]
    fn test_type_registry_lookup() {
        let registry = TypeRegistry::new();

        // Primary type names with bit-width
        assert_eq!(registry.lookup("i64"), Some(TypeId::I64));
        assert_eq!(registry.lookup("i32"), Some(TypeId::I32));
        assert_eq!(registry.lookup("f64"), Some(TypeId::F64));
        assert_eq!(registry.lookup("f32"), Some(TypeId::F32));
        assert_eq!(registry.lookup("bool"), Some(TypeId::BOOL));
        assert_eq!(registry.lookup("str"), Some(TypeId::STRING));
        assert_eq!(registry.lookup("Nonexistent"), None);
    }

    #[test]
    fn test_all_numeric_types() {
        let registry = TypeRegistry::new();

        // Signed integers
        assert_eq!(registry.lookup("i8"), Some(TypeId::I8));
        assert_eq!(registry.lookup("i16"), Some(TypeId::I16));
        assert_eq!(registry.lookup("i32"), Some(TypeId::I32));
        assert_eq!(registry.lookup("i64"), Some(TypeId::I64));

        // Unsigned integers
        assert_eq!(registry.lookup("u8"), Some(TypeId::U8));
        assert_eq!(registry.lookup("u16"), Some(TypeId::U16));
        assert_eq!(registry.lookup("u32"), Some(TypeId::U32));
        assert_eq!(registry.lookup("u64"), Some(TypeId::U64));

        // Floats
        assert_eq!(registry.lookup("f32"), Some(TypeId::F32));
        assert_eq!(registry.lookup("f64"), Some(TypeId::F64));
    }

    #[test]
    fn test_type_registry_register() {
        let mut registry = TypeRegistry::new();

        let struct_type = HirType::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), TypeId::F64),
                ("y".to_string(), TypeId::F64),
            ],
            has_snapshot: false,
        };

        let id = registry.register_named("Point".to_string(), struct_type.clone());
        assert_eq!(registry.get(id), Some(&struct_type));
        assert_eq!(registry.lookup("Point"), Some(id));
    }

    #[test]
    fn test_hir_expr_integer() {
        let expr = HirExpr {
            kind: HirExprKind::Integer(42),
            ty: TypeId::I64,
        };

        assert_eq!(expr.ty, TypeId::I64);
        if let HirExprKind::Integer(n) = expr.kind {
            assert_eq!(n, 42);
        } else {
            panic!("Expected Integer");
        }
    }

    #[test]
    fn test_hir_expr_binary() {
        let left = Box::new(HirExpr {
            kind: HirExprKind::Integer(1),
            ty: TypeId::I64,
        });
        let right = Box::new(HirExpr {
            kind: HirExprKind::Integer(2),
            ty: TypeId::I64,
        });

        let expr = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Add,
                left,
                right,
            },
            ty: TypeId::I64,
        };

        assert_eq!(expr.ty, TypeId::I64);
    }

    #[test]
    fn test_hir_function() {
        let func = HirFunction {
            name: "add".to_string(),
            params: vec![
                LocalVar {
                    name: "a".to_string(),
                    ty: TypeId::I64,
                    mutability: Mutability::Immutable,
                    inject: false,
                    is_ghost: false,
                },
                LocalVar {
                    name: "b".to_string(),
                    ty: TypeId::I64,
                    mutability: Mutability::Immutable,
                    inject: false,
                    is_ghost: false,
                },
            ],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![HirStmt::Return(Some(HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Add,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(0),
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Local(1),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::I64,
            }))],
            visibility: Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: VerificationMode::default(),
            is_ghost: false,
        };

        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.return_type, TypeId::I64);
        assert!(func.is_public());
        assert!(!func.params[0].is_mutable());
        // Default layout phase is Steady
        assert_eq!(func.layout_phase(), LayoutPhase::Steady);
        assert!(!func.is_event_loop_anchor());
        // Default verification mode is Unverified
        assert!(!func.is_verified());
    }

    #[test]
    fn test_hir_module() {
        let module = HirModule::new();

        assert!(module.name.is_none());
        assert!(module.functions.is_empty());
        assert!(module.globals.is_empty());
        // Verify builtin types are registered with lowercase names
        assert!(module.types.lookup("i64").is_some());
        assert!(module.types.lookup("bool").is_some());
        assert!(module.types.lookup("str").is_some());
    }
}
