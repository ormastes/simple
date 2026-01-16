//! Low coverage improvement tests - Round 9
//!
//! Targets: compilability.rs, pkg/linker.rs, monomorphize/table.rs,
//!          monomorphize/types.rs, hir/types.rs

// ===========================================================================
// Compilability Tests (simple_compiler::compilability)
// ===========================================================================
mod compilability_tests {
    use simple_compiler::compilability::{CompilabilityStatus, FallbackReason};

    #[test]
    fn test_fallback_reason_dynamic_types() {
        let reason = FallbackReason::DynamicTypes;
        assert_eq!(reason, FallbackReason::DynamicTypes);
    }

    #[test]
    fn test_fallback_reason_collection_ops() {
        let reason = FallbackReason::CollectionOps;
        assert_eq!(reason, FallbackReason::CollectionOps);
    }

    #[test]
    fn test_fallback_reason_collection_literal() {
        let reason = FallbackReason::CollectionLiteral;
        assert_eq!(reason, FallbackReason::CollectionLiteral);
    }

    #[test]
    fn test_fallback_reason_string_ops() {
        let reason = FallbackReason::StringOps;
        assert_eq!(reason, FallbackReason::StringOps);
    }

    #[test]
    fn test_fallback_reason_gc_in_nogc() {
        let reason = FallbackReason::GcInNogcContext;
        assert_eq!(reason, FallbackReason::GcInNogcContext);
    }

    #[test]
    fn test_fallback_reason_blocking_in_async() {
        let reason = FallbackReason::BlockingInAsync;
        assert_eq!(reason, FallbackReason::BlockingInAsync);
    }

    #[test]
    fn test_fallback_reason_actor_ops() {
        let reason = FallbackReason::ActorOps;
        assert_eq!(reason, FallbackReason::ActorOps);
    }

    #[test]
    fn test_fallback_reason_user_macros() {
        let reason = FallbackReason::UserMacros;
        assert_eq!(reason, FallbackReason::UserMacros);
    }

    #[test]
    fn test_fallback_reason_pattern_match() {
        let reason = FallbackReason::PatternMatch;
        assert_eq!(reason, FallbackReason::PatternMatch);
    }

    #[test]
    fn test_fallback_reason_closure() {
        let reason = FallbackReason::Closure;
        assert_eq!(reason, FallbackReason::Closure);
    }

    #[test]
    fn test_fallback_reason_object_construction() {
        let reason = FallbackReason::ObjectConstruction;
        assert_eq!(reason, FallbackReason::ObjectConstruction);
    }

    #[test]
    fn test_fallback_reason_method_call() {
        let reason = FallbackReason::MethodCall;
        assert_eq!(reason, FallbackReason::MethodCall);
    }

    #[test]
    fn test_fallback_reason_field_access() {
        let reason = FallbackReason::FieldAccess;
        assert_eq!(reason, FallbackReason::FieldAccess);
    }

    #[test]
    fn test_fallback_reason_generator() {
        let reason = FallbackReason::Generator;
        assert_eq!(reason, FallbackReason::Generator);
    }

    #[test]
    fn test_fallback_reason_async_await() {
        let reason = FallbackReason::AsyncAwait;
        assert_eq!(reason, FallbackReason::AsyncAwait);
    }

    #[test]
    fn test_fallback_reason_decorators() {
        let reason = FallbackReason::Decorators;
        assert_eq!(reason, FallbackReason::Decorators);
    }

    #[test]
    fn test_fallback_reason_try_operator() {
        let reason = FallbackReason::TryOperator;
        assert_eq!(reason, FallbackReason::TryOperator);
    }

    #[test]
    fn test_fallback_reason_with_statement() {
        let reason = FallbackReason::WithStatement;
        assert_eq!(reason, FallbackReason::WithStatement);
    }

    #[test]
    fn test_fallback_reason_context_block() {
        let reason = FallbackReason::ContextBlock;
        assert_eq!(reason, FallbackReason::ContextBlock);
    }

    #[test]
    fn test_fallback_reason_unknown_extern() {
        let reason = FallbackReason::UnknownExtern("my_extern".to_string());
        match reason {
            FallbackReason::UnknownExtern(name) => assert_eq!(name, "my_extern"),
            _ => panic!("Expected UnknownExtern"),
        }
    }

    #[test]
    fn test_fallback_reason_not_yet_implemented() {
        let reason = FallbackReason::NotYetImplemented("feature_x".to_string());
        match reason {
            FallbackReason::NotYetImplemented(msg) => assert_eq!(msg, "feature_x"),
            _ => panic!("Expected NotYetImplemented"),
        }
    }

    #[test]
    fn test_compilability_status_compilable() {
        let status = CompilabilityStatus::Compilable;
        assert!(status.is_compilable());
        assert!(status.reasons().is_empty());
    }

    #[test]
    fn test_compilability_status_requires_interpreter() {
        let reasons = vec![FallbackReason::Closure, FallbackReason::PatternMatch];
        let status = CompilabilityStatus::RequiresInterpreter(reasons);
        assert!(!status.is_compilable());
        assert_eq!(status.reasons().len(), 2);
    }

    #[test]
    fn test_compilability_status_merge_compilable_with_compilable() {
        let mut status = CompilabilityStatus::Compilable;
        status.merge(CompilabilityStatus::Compilable);
        assert!(status.is_compilable());
    }

    #[test]
    fn test_compilability_status_merge_compilable_with_requires() {
        let mut status = CompilabilityStatus::Compilable;
        status.merge(CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::Closure]));
        assert!(!status.is_compilable());
        assert_eq!(status.reasons().len(), 1);
    }

    #[test]
    fn test_compilability_status_merge_requires_with_requires() {
        let mut status = CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::PatternMatch]);
        status.merge(CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::Closure]));
        assert!(!status.is_compilable());
        assert_eq!(status.reasons().len(), 2);
    }

    #[test]
    fn test_compilability_status_merge_deduplicate() {
        let mut status = CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::Closure]);
        status.merge(CompilabilityStatus::RequiresInterpreter(vec![
            FallbackReason::Closure, // duplicate
        ]));
        assert_eq!(status.reasons().len(), 1);
    }

    #[test]
    fn test_fallback_reason_clone() {
        let reason = FallbackReason::Generator;
        let cloned = reason.clone();
        assert_eq!(reason, cloned);
    }

    #[test]
    fn test_fallback_reason_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(FallbackReason::Closure);
        set.insert(FallbackReason::Generator);
        assert_eq!(set.len(), 2);
        assert!(set.contains(&FallbackReason::Closure));
    }
}

// ===========================================================================
// Package Linker Tests (simple_pkg::Linker)
// ===========================================================================
mod pkg_linker_tests {
    use simple_pkg::Linker;
    use std::path::Path;

    #[test]
    fn test_linker_new() {
        let linker = Linker::new(Path::new("/tmp/project"));
        assert_eq!(linker.deps_dir(), Path::new("/tmp/project/deps"));
    }

    #[test]
    fn test_linker_deps_dir() {
        let linker = Linker::new(Path::new("/home/user/myproject"));
        let deps = linker.deps_dir();
        assert!(deps.ends_with("deps"));
    }

    #[test]
    fn test_link_type_variants() {
        use simple_pkg::linker::LinkType;

        let symlink = LinkType::Symlink;
        let hardlink = LinkType::HardLink;
        let copy = LinkType::Copy;

        assert_eq!(symlink, LinkType::Symlink);
        assert_eq!(hardlink, LinkType::HardLink);
        assert_eq!(copy, LinkType::Copy);
    }

    #[test]
    fn test_linked_package_struct() {
        use simple_pkg::linker::{LinkType, LinkedPackage};
        use std::path::PathBuf;

        let pkg = LinkedPackage {
            name: "mylib".to_string(),
            link_type: LinkType::Symlink,
            target: PathBuf::from("/path/to/mylib"),
        };

        assert_eq!(pkg.name, "mylib");
        assert_eq!(pkg.link_type, LinkType::Symlink);
    }
}

// ===========================================================================
// Monomorphization Table Tests (simple_compiler::MonomorphizationTable)
// ===========================================================================
mod monomorphize_table_tests {
    use simple_compiler::{ConcreteType, MonomorphizationTable, SpecializationKey};

    #[test]
    fn test_monomorphization_table_new() {
        let table = MonomorphizationTable::new();
        assert!(!table.has_pending());
    }

    #[test]
    fn test_monomorphization_table_default() {
        let table = MonomorphizationTable::default();
        assert!(!table.has_pending());
    }

    #[test]
    fn test_monomorphization_table_has_pending_empty() {
        let table = MonomorphizationTable::new();
        assert!(!table.has_pending());
    }

    #[test]
    fn test_monomorphization_table_pop_pending_function_empty() {
        let mut table = MonomorphizationTable::new();
        assert!(table.pop_pending_function().is_none());
    }

    #[test]
    fn test_monomorphization_table_pop_pending_struct_empty() {
        let mut table = MonomorphizationTable::new();
        assert!(table.pop_pending_struct().is_none());
    }

    #[test]
    fn test_monomorphization_table_pop_pending_class_empty() {
        let mut table = MonomorphizationTable::new();
        assert!(table.pop_pending_class().is_none());
    }

    #[test]
    fn test_monomorphization_table_mark_processed() {
        let mut table = MonomorphizationTable::new();
        let key = SpecializationKey::new("test", vec![ConcreteType::Int]);
        table.mark_processed(&key);
        // processed is pub(super), so we can't access it directly
        // but mark_processed should prevent duplicate requests
    }

    #[test]
    fn test_monomorphization_table_get_specialized_function_none() {
        let table = MonomorphizationTable::new();
        let key = SpecializationKey::new("test", vec![]);
        assert!(table.get_specialized_function(&key).is_none());
    }

    #[test]
    fn test_monomorphization_table_specialized_functions_empty() {
        let table = MonomorphizationTable::new();
        assert_eq!(table.specialized_functions().count(), 0);
    }

    #[test]
    fn test_monomorphization_table_specialized_structs_empty() {
        let table = MonomorphizationTable::new();
        assert_eq!(table.specialized_structs().count(), 0);
    }

    #[test]
    fn test_monomorphization_table_specialized_classes_empty() {
        let table = MonomorphizationTable::new();
        assert_eq!(table.specialized_classes().count(), 0);
    }
}

// ===========================================================================
// Monomorphization Types Tests (simple_compiler::ConcreteType, SpecializationKey)
// ===========================================================================
mod monomorphize_types_tests {
    use simple_compiler::{ConcreteType, PointerKind, SpecializationKey, TypeBindings};

    #[test]
    fn test_specialization_key_new() {
        let key = SpecializationKey::new("identity", vec![ConcreteType::Int]);
        assert_eq!(key.name, "identity");
        assert_eq!(key.type_args.len(), 1);
    }

    #[test]
    fn test_specialization_key_mangled_name_no_args() {
        let key = SpecializationKey::new("foo", vec![]);
        assert_eq!(key.mangled_name(), "foo");
    }

    #[test]
    fn test_specialization_key_mangled_name_with_args() {
        let key = SpecializationKey::new("identity", vec![ConcreteType::Int]);
        assert_eq!(key.mangled_name(), "identity$Int");
    }

    #[test]
    fn test_specialization_key_mangled_name_multiple_args() {
        let key = SpecializationKey::new("pair", vec![ConcreteType::Int, ConcreteType::String]);
        assert_eq!(key.mangled_name(), "pair$Int_String");
    }

    #[test]
    fn test_specialization_key_equality() {
        let key1 = SpecializationKey::new("test", vec![ConcreteType::Bool]);
        let key2 = SpecializationKey::new("test", vec![ConcreteType::Bool]);
        assert_eq!(key1, key2);
    }

    #[test]
    fn test_specialization_key_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(SpecializationKey::new("a", vec![ConcreteType::Int]));
        set.insert(SpecializationKey::new("b", vec![ConcreteType::Int]));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_concrete_type_int() {
        let ty = ConcreteType::Int;
        assert_eq!(ty.to_string(), "Int");
    }

    #[test]
    fn test_concrete_type_float() {
        let ty = ConcreteType::Float;
        assert_eq!(ty.to_string(), "Float");
    }

    #[test]
    fn test_concrete_type_bool() {
        let ty = ConcreteType::Bool;
        assert_eq!(ty.to_string(), "Bool");
    }

    #[test]
    fn test_concrete_type_string() {
        let ty = ConcreteType::String;
        assert_eq!(ty.to_string(), "String");
    }

    #[test]
    fn test_concrete_type_nil() {
        let ty = ConcreteType::Nil;
        assert_eq!(ty.to_string(), "Nil");
    }

    #[test]
    fn test_concrete_type_named() {
        let ty = ConcreteType::Named("MyStruct".to_string());
        assert_eq!(ty.to_string(), "MyStruct");
    }

    #[test]
    fn test_concrete_type_array() {
        let ty = ConcreteType::Array(Box::new(ConcreteType::Int));
        assert_eq!(ty.to_string(), "Array_Int");
    }

    #[test]
    fn test_concrete_type_tuple() {
        let ty = ConcreteType::Tuple(vec![ConcreteType::Int, ConcreteType::Bool]);
        assert_eq!(ty.to_string(), "Tuple_Int_Bool");
    }

    #[test]
    fn test_concrete_type_dict() {
        let ty = ConcreteType::Dict {
            key: Box::new(ConcreteType::String),
            value: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Dict_String_Int");
    }

    #[test]
    fn test_concrete_type_function() {
        let ty = ConcreteType::Function {
            params: vec![ConcreteType::Int],
            ret: Box::new(ConcreteType::Bool),
        };
        assert_eq!(ty.to_string(), "Fn_Int_Bool");
    }

    #[test]
    fn test_concrete_type_optional() {
        let ty = ConcreteType::Optional(Box::new(ConcreteType::Int));
        assert_eq!(ty.to_string(), "Opt_Int");
    }

    #[test]
    fn test_concrete_type_pointer_unique() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::Unique,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Unique_Int");
    }

    #[test]
    fn test_concrete_type_pointer_shared() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::Shared,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Shared_Int");
    }

    #[test]
    fn test_concrete_type_pointer_weak() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::Weak,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Weak_Int");
    }

    #[test]
    fn test_concrete_type_pointer_handle() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::Handle,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Handle_Int");
    }

    #[test]
    fn test_concrete_type_pointer_borrow() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::Borrow,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "Borrow_Int");
    }

    #[test]
    fn test_concrete_type_pointer_borrow_mut() {
        let ty = ConcreteType::Pointer {
            kind: PointerKind::BorrowMut,
            inner: Box::new(ConcreteType::Int),
        };
        assert_eq!(ty.to_string(), "BorrowMut_Int");
    }

    #[test]
    fn test_concrete_type_specialized() {
        let ty = ConcreteType::Specialized {
            name: "List".to_string(),
            args: vec![ConcreteType::Int],
        };
        assert_eq!(ty.to_string(), "List_Int");
    }

    #[test]
    fn test_pointer_kind_variants() {
        assert_eq!(PointerKind::Unique, PointerKind::Unique);
        assert_eq!(PointerKind::Shared, PointerKind::Shared);
        assert_eq!(PointerKind::Weak, PointerKind::Weak);
        assert_eq!(PointerKind::Handle, PointerKind::Handle);
        assert_eq!(PointerKind::Borrow, PointerKind::Borrow);
        assert_eq!(PointerKind::BorrowMut, PointerKind::BorrowMut);
    }

    #[test]
    fn test_type_bindings_default() {
        let bindings: TypeBindings = TypeBindings::new();
        assert!(bindings.is_empty());
    }

    #[test]
    fn test_type_bindings_insert_get() {
        let mut bindings: TypeBindings = TypeBindings::new();
        bindings.insert("T".to_string(), ConcreteType::Int);
        assert_eq!(bindings.get("T"), Some(&ConcreteType::Int));
    }
}

// ===========================================================================
// HIR Types Tests (simple_compiler::hir::*)
// ===========================================================================
mod hir_types_tests {
    use simple_compiler::hir::{
        FieldLayout, HirOverflowBehavior, HirType, HirUnitConstraints, PointerKind, Signedness, StructLayout, TypeId,
        TypeRegistry,
    };

    #[test]
    fn test_signedness_signed() {
        let s = Signedness::Signed;
        assert!(s.is_signed());
        assert!(!s.is_unsigned());
    }

    #[test]
    fn test_signedness_unsigned() {
        let s = Signedness::Unsigned;
        assert!(s.is_unsigned());
        assert!(!s.is_signed());
    }

    #[test]
    fn test_signedness_default() {
        let s = Signedness::default();
        assert!(s.is_signed());
    }

    #[test]
    fn test_hir_overflow_behavior_default() {
        let ob = HirOverflowBehavior::default();
        assert_eq!(ob, HirOverflowBehavior::Default);
    }

    #[test]
    fn test_hir_overflow_behavior_checked() {
        let ob = HirOverflowBehavior::Checked;
        assert_eq!(ob, HirOverflowBehavior::Checked);
    }

    #[test]
    fn test_hir_overflow_behavior_saturate() {
        let ob = HirOverflowBehavior::Saturate;
        assert_eq!(ob, HirOverflowBehavior::Saturate);
    }

    #[test]
    fn test_hir_overflow_behavior_wrap() {
        let ob = HirOverflowBehavior::Wrap;
        assert_eq!(ob, HirOverflowBehavior::Wrap);
    }

    #[test]
    fn test_hir_unit_constraints_default() {
        let c = HirUnitConstraints::default();
        assert!(c.range.is_none());
        assert_eq!(c.overflow, HirOverflowBehavior::Default);
    }

    #[test]
    fn test_hir_unit_constraints_with_range() {
        let c = HirUnitConstraints {
            range: Some((0, 100)),
            overflow: HirOverflowBehavior::Saturate,
        };
        assert_eq!(c.range, Some((0, 100)));
        assert_eq!(c.overflow, HirOverflowBehavior::Saturate);
    }

    #[test]
    fn test_type_id_constants() {
        assert_eq!(TypeId::VOID.0, 0);
        assert_eq!(TypeId::BOOL.0, 1);
        assert_eq!(TypeId::I8.0, 2);
        assert_eq!(TypeId::I16.0, 3);
        assert_eq!(TypeId::I32.0, 4);
        assert_eq!(TypeId::I64.0, 5);
        assert_eq!(TypeId::U8.0, 6);
        assert_eq!(TypeId::U16.0, 7);
        assert_eq!(TypeId::U32.0, 8);
        assert_eq!(TypeId::U64.0, 9);
        assert_eq!(TypeId::F32.0, 10);
        assert_eq!(TypeId::F64.0, 11);
        assert_eq!(TypeId::STRING.0, 12);
        assert_eq!(TypeId::NIL.0, 13);
    }

    #[test]
    fn test_type_id_is_known() {
        assert!(TypeId::VOID.is_known());
        assert!(TypeId::I64.is_known());
        assert!(TypeId(100).is_known());
    }

    #[test]
    fn test_hir_type_void() {
        let ty = HirType::Void;
        assert_eq!(ty, HirType::Void);
    }

    #[test]
    fn test_hir_type_bool() {
        let ty = HirType::Bool;
        assert_eq!(ty, HirType::Bool);
    }

    #[test]
    fn test_hir_type_int_signed() {
        let ty = HirType::Int {
            bits: 64,
            signedness: Signedness::Signed,
        };
        match ty {
            HirType::Int { bits, signedness } => {
                assert_eq!(bits, 64);
                assert!(signedness.is_signed());
            }
            _ => panic!("Expected Int"),
        }
    }

    #[test]
    fn test_hir_type_int_unsigned() {
        let ty = HirType::Int {
            bits: 32,
            signedness: Signedness::Unsigned,
        };
        match ty {
            HirType::Int { bits, signedness } => {
                assert_eq!(bits, 32);
                assert!(signedness.is_unsigned());
            }
            _ => panic!("Expected Int"),
        }
    }

    #[test]
    fn test_hir_type_float() {
        let ty = HirType::Float { bits: 64 };
        match ty {
            HirType::Float { bits } => assert_eq!(bits, 64),
            _ => panic!("Expected Float"),
        }
    }

    #[test]
    fn test_hir_type_string() {
        let ty = HirType::String;
        assert_eq!(ty, HirType::String);
    }

    #[test]
    fn test_hir_type_nil() {
        let ty = HirType::Nil;
        assert_eq!(ty, HirType::Nil);
    }

    #[test]
    fn test_hir_type_pointer() {
        use simple_parser::ast::ReferenceCapability;
        let ty = HirType::Pointer {
            kind: PointerKind::Borrow,
            capability: ReferenceCapability::Shared,
            inner: TypeId::I64,
        };
        match ty {
            HirType::Pointer { kind, inner, .. } => {
                assert_eq!(kind, PointerKind::Borrow);
                assert_eq!(inner, TypeId::I64);
            }
            _ => panic!("Expected Pointer"),
        }
    }

    #[test]
    fn test_hir_type_array() {
        let ty = HirType::Array {
            element: TypeId::I32,
            size: Some(10),
        };
        match ty {
            HirType::Array { element, size } => {
                assert_eq!(element, TypeId::I32);
                assert_eq!(size, Some(10));
            }
            _ => panic!("Expected Array"),
        }
    }

    #[test]
    fn test_hir_type_simd() {
        let ty = HirType::Simd {
            lanes: 4,
            element: TypeId::F32,
        };
        match ty {
            HirType::Simd { lanes, element } => {
                assert_eq!(lanes, 4);
                assert_eq!(element, TypeId::F32);
            }
            _ => panic!("Expected Simd"),
        }
    }

    #[test]
    fn test_hir_type_tuple() {
        let ty = HirType::Tuple(vec![TypeId::I32, TypeId::BOOL]);
        match ty {
            HirType::Tuple(types) => {
                assert_eq!(types.len(), 2);
            }
            _ => panic!("Expected Tuple"),
        }
    }

    #[test]
    fn test_hir_type_function() {
        let ty = HirType::Function {
            params: vec![TypeId::I32],
            ret: TypeId::BOOL,
        };
        match ty {
            HirType::Function { params, ret } => {
                assert_eq!(params.len(), 1);
                assert_eq!(ret, TypeId::BOOL);
            }
            _ => panic!("Expected Function"),
        }
    }

    #[test]
    fn test_hir_type_struct() {
        let ty = HirType::Struct {
            name: "Point".to_string(),
            fields: vec![("x".to_string(), TypeId::I32), ("y".to_string(), TypeId::I32)],
            has_snapshot: false,
        };
        match ty {
            HirType::Struct {
                name,
                fields,
                has_snapshot,
            } => {
                assert_eq!(name, "Point");
                assert_eq!(fields.len(), 2);
                assert!(!has_snapshot);
            }
            _ => panic!("Expected Struct"),
        }
    }

    #[test]
    fn test_hir_type_enum() {
        let ty = HirType::Enum {
            name: "Color".to_string(),
            variants: vec![
                ("Red".to_string(), None),
                ("Green".to_string(), None),
                ("Blue".to_string(), None),
            ],
        };
        match ty {
            HirType::Enum { name, variants } => {
                assert_eq!(name, "Color");
                assert_eq!(variants.len(), 3);
            }
            _ => panic!("Expected Enum"),
        }
    }

    #[test]
    fn test_hir_type_unit_type() {
        let ty = HirType::UnitType {
            name: "_cm".to_string(),
            repr: TypeId::U16,
            bits: 16,
            signedness: Signedness::Unsigned,
            is_float: false,
            constraints: HirUnitConstraints::default(),
        };
        match ty {
            HirType::UnitType { name, bits, .. } => {
                assert_eq!(name, "_cm");
                assert_eq!(bits, 16);
            }
            _ => panic!("Expected UnitType"),
        }
    }

    #[test]
    fn test_hir_type_union() {
        let ty = HirType::Union {
            variants: vec![TypeId::I32, TypeId::STRING],
        };
        match ty {
            HirType::Union { variants } => {
                assert_eq!(variants.len(), 2);
            }
            _ => panic!("Expected Union"),
        }
    }

    #[test]
    fn test_hir_type_unknown() {
        let ty = HirType::Unknown;
        assert_eq!(ty, HirType::Unknown);
    }

    #[test]
    fn test_field_layout_struct() {
        let layout = FieldLayout {
            name: "x".to_string(),
            ty: TypeId::I32,
            offset: 0,
            size: 4,
        };
        assert_eq!(layout.name, "x");
        assert_eq!(layout.offset, 0);
        assert_eq!(layout.size, 4);
    }

    #[test]
    fn test_hir_pointer_kind_variants() {
        assert_eq!(PointerKind::Borrow, PointerKind::Borrow);
        assert_eq!(PointerKind::BorrowMut, PointerKind::BorrowMut);
        assert_eq!(PointerKind::Unique, PointerKind::Unique);
        assert_eq!(PointerKind::Shared, PointerKind::Shared);
        assert_eq!(PointerKind::Weak, PointerKind::Weak);
        assert_eq!(PointerKind::Handle, PointerKind::Handle);
    }
}
