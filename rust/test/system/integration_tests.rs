#![allow(unused_imports, unused_variables, deprecated)]
//! Integration tests: HIR types, ExecCore, data structures
//! Tests for compiler internals integration

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// HIR Types Integration Tests
// =============================================================================

use simple_compiler::hir::{
    BinOp, HirExpr, HirExprKind, HirFunction, HirModule, HirStmt, HirType, LocalVar, PointerKind, Signedness, TypeId,
    TypeIdAllocator, TypeRegistry, UnaryOp,
};
use simple_parser::ast::{Mutability, Visibility};

/// Test TypeRegistry initialization with builtins
#[test]
fn test_type_registry_builtins_integration() {
    let registry = TypeRegistry::new();

    // Test all builtin type IDs
    assert!(registry.get(TypeId::VOID).is_some());
    assert!(registry.get(TypeId::BOOL).is_some());
    assert!(registry.get(TypeId::I8).is_some());
    assert!(registry.get(TypeId::I16).is_some());
    assert!(registry.get(TypeId::I32).is_some());
    assert!(registry.get(TypeId::I64).is_some());
    assert!(registry.get(TypeId::U8).is_some());
    assert!(registry.get(TypeId::U16).is_some());
    assert!(registry.get(TypeId::U32).is_some());
    assert!(registry.get(TypeId::U64).is_some());
    assert!(registry.get(TypeId::F32).is_some());
    assert!(registry.get(TypeId::F64).is_some());
    assert!(registry.get(TypeId::STRING).is_some());
    assert!(registry.get(TypeId::NIL).is_some());
}

/// Test TypeRegistry lookup by name
#[test]
fn test_type_registry_lookup_integration() {
    let registry = TypeRegistry::new();

    assert_eq!(registry.lookup("void"), Some(TypeId::VOID));
    assert_eq!(registry.lookup("bool"), Some(TypeId::BOOL));
    assert_eq!(registry.lookup("i8"), Some(TypeId::I8));
    assert_eq!(registry.lookup("i16"), Some(TypeId::I16));
    assert_eq!(registry.lookup("i32"), Some(TypeId::I32));
    assert_eq!(registry.lookup("i64"), Some(TypeId::I64));
    assert_eq!(registry.lookup("u8"), Some(TypeId::U8));
    assert_eq!(registry.lookup("u16"), Some(TypeId::U16));
    assert_eq!(registry.lookup("u32"), Some(TypeId::U32));
    assert_eq!(registry.lookup("u64"), Some(TypeId::U64));
    assert_eq!(registry.lookup("f32"), Some(TypeId::F32));
    assert_eq!(registry.lookup("f64"), Some(TypeId::F64));
    assert_eq!(registry.lookup("str"), Some(TypeId::STRING));
    assert_eq!(registry.lookup("nil"), Some(TypeId::NIL));
    assert_eq!(registry.lookup("nonexistent"), None);
}

/// Test TypeRegistry register and register_named
#[test]
fn test_type_registry_register_integration() {
    let mut registry = TypeRegistry::new();

    // Register anonymous type
    let array_type = HirType::Array {
        element: TypeId::I32,
        size: Some(10),
    };
    let array_id = registry.register(array_type.clone());
    assert_eq!(registry.get(array_id), Some(&array_type));

    // Register named type
    let struct_type = HirType::Struct {
        name: "Point".to_string(),
        fields: vec![("x".to_string(), TypeId::F64), ("y".to_string(), TypeId::F64)],
        has_snapshot: false,
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    };
    let struct_id = registry.register_named("Point".to_string(), struct_type.clone());
    assert_eq!(registry.get(struct_id), Some(&struct_type));
    assert_eq!(registry.lookup("Point"), Some(struct_id));
}

/// Test TypeIdAllocator
#[test]
fn test_type_id_allocator_integration() {
    let mut allocator = TypeIdAllocator::new();

    // Allocator starts after builtins
    assert_eq!(allocator.peek_next(), 14);

    let id1 = allocator.alloc();
    assert_eq!(id1.0, 14);

    let id2 = allocator.alloc();
    assert_eq!(id2.0, 15);

    let id3 = allocator.alloc();
    assert_eq!(id3.0, 16);

    // Custom start
    let mut custom_allocator = TypeIdAllocator::with_start(100);
    assert_eq!(custom_allocator.peek_next(), 100);
    let custom_id = custom_allocator.alloc();
    assert_eq!(custom_id.0, 100);
}

/// Test TypeId constants
#[test]
fn test_type_id_constants_integration() {
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

    // Test is_known
    assert!(TypeId::I32.is_known());
    assert!(TypeId::VOID.is_known());
}

/// Test HirType constructors
#[test]
fn test_hir_type_constructors_integration() {
    // Signed int
    let signed = HirType::signed_int(32);
    assert_eq!(
        signed,
        HirType::Int {
            bits: 32,
            signedness: Signedness::Signed
        }
    );

    // Unsigned int
    let unsigned = HirType::unsigned_int(64);
    assert_eq!(
        unsigned,
        HirType::Int {
            bits: 64,
            signedness: Signedness::Unsigned
        }
    );
}

/// Test Signedness enum
#[test]
fn test_signedness_integration() {
    assert!(Signedness::Signed.is_signed());
    assert!(!Signedness::Signed.is_unsigned());
    assert!(!Signedness::Unsigned.is_signed());
    assert!(Signedness::Unsigned.is_unsigned());
    assert_eq!(Signedness::default(), Signedness::Signed);
}

/// Test HirExpr construction
#[test]
fn test_hir_expr_construction_integration() {
    // Integer literal
    let int_expr = HirExpr {
        kind: HirExprKind::Integer(42),
        ty: TypeId::I64,
    };
    assert_eq!(int_expr.ty, TypeId::I64);

    // Float literal
    let float_expr = HirExpr {
        kind: HirExprKind::Float(3.15),
        ty: TypeId::F64,
    };
    assert_eq!(float_expr.ty, TypeId::F64);

    // Bool literal
    let bool_expr = HirExpr {
        kind: HirExprKind::Bool(true),
        ty: TypeId::BOOL,
    };
    assert_eq!(bool_expr.ty, TypeId::BOOL);

    // String literal
    let str_expr = HirExpr {
        kind: HirExprKind::String("hello".to_string()),
        ty: TypeId::STRING,
    };
    assert_eq!(str_expr.ty, TypeId::STRING);

    // Nil literal
    let nil_expr = HirExpr {
        kind: HirExprKind::Nil,
        ty: TypeId::NIL,
    };
    assert_eq!(nil_expr.ty, TypeId::NIL);
}

/// Test HirExpr binary operations
#[test]
fn test_hir_expr_binary_integration() {
    let left = Box::new(HirExpr {
        kind: HirExprKind::Integer(10),
        ty: TypeId::I64,
    });
    let right = Box::new(HirExpr {
        kind: HirExprKind::Integer(20),
        ty: TypeId::I64,
    });

    let add_expr = HirExpr {
        kind: HirExprKind::Binary {
            op: BinOp::Add,
            left: left.clone(),
            right: right.clone(),
        },
        ty: TypeId::I64,
    };

    if let HirExprKind::Binary { op, .. } = &add_expr.kind {
        assert_eq!(*op, BinOp::Add);
    } else {
        panic!("Expected Binary expression");
    }
}

/// Test HirExpr unary operations
#[test]
fn test_hir_expr_unary_integration() {
    let operand = Box::new(HirExpr {
        kind: HirExprKind::Integer(5),
        ty: TypeId::I64,
    });

    let neg_expr = HirExpr {
        kind: HirExprKind::Unary {
            op: UnaryOp::Neg,
            operand,
        },
        ty: TypeId::I64,
    };

    if let HirExprKind::Unary { op, .. } = &neg_expr.kind {
        assert_eq!(*op, UnaryOp::Neg);
    } else {
        panic!("Expected Unary expression");
    }
}

/// Test HirStmt construction
#[test]
fn test_hir_stmt_construction_integration() {
    // Let statement
    let let_stmt = HirStmt::Let {
        local_index: 0,
        ty: TypeId::I64,
        value: Some(HirExpr {
            kind: HirExprKind::Integer(42),
            ty: TypeId::I64,
        }),
    };
    assert!(matches!(let_stmt, HirStmt::Let { local_index: 0, .. }));

    // Return statement
    let return_stmt = HirStmt::Return(Some(HirExpr {
        kind: HirExprKind::Integer(0),
        ty: TypeId::I64,
    }));
    assert!(matches!(return_stmt, HirStmt::Return(Some(_))));

    // Control flow
    let break_stmt = HirStmt::Break;
    let continue_stmt = HirStmt::Continue;
    assert!(matches!(break_stmt, HirStmt::Break));
    assert!(matches!(continue_stmt, HirStmt::Continue));
}

/// Test LocalVar construction
#[test]
fn test_local_var_integration() {
    let mutable_var = LocalVar {
        name: "x".to_string(),
        ty: TypeId::I64,
        mutability: Mutability::Mutable,
        inject: false,
        is_ghost: false,
    };
    assert!(mutable_var.is_mutable());

    let immutable_var = LocalVar {
        name: "y".to_string(),
        ty: TypeId::F64,
        mutability: Mutability::Immutable,
        inject: false,
        is_ghost: false,
    };
    assert!(!immutable_var.is_mutable());
}

/// Test HirFunction construction
#[test]
fn test_hir_function_integration() {
    use simple_compiler::hir::{ConcurrencyMode, VerificationMode};
    let func = HirFunction {
        name: "add".to_string(),
        span: None,
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
        verification_mode: VerificationMode::Unverified,
        is_ghost: false,
        has_suspension: false,
        is_sync: false,
    };

    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 2);
    assert_eq!(func.return_type, TypeId::I64);
    assert!(func.is_public());
}

/// Test HirModule construction
#[test]
fn test_hir_module_integration() {
    let module = HirModule::new();
    assert!(module.name.is_none());
    assert!(module.functions.is_empty());
    assert!(module.globals.is_empty());
    // Verify builtins are registered
    assert!(module.types.lookup("i64").is_some());
}

/// Test HirModule default trait
#[test]
fn test_hir_module_default_integration() {
    let module: HirModule = Default::default();
    assert!(module.name.is_none());
}

/// Test PointerKind variants
#[test]
fn test_pointer_kind_integration() {
    use simple_parser::ast::ReferenceCapability;
    let kinds = [
        PointerKind::Unique,
        PointerKind::Shared,
        PointerKind::Weak,
        PointerKind::Handle,
        PointerKind::Borrow,
        PointerKind::BorrowMut,
    ];

    for kind in &kinds {
        let ptr_type = HirType::Pointer {
            kind: *kind,
            capability: ReferenceCapability::Shared,
            inner: TypeId::I32,
        };
        if let HirType::Pointer { kind: k, inner, .. } = ptr_type {
            assert_eq!(k, *kind);
            assert_eq!(inner, TypeId::I32);
        }
    }
}

// =============================================================================
// MIR Types Integration Tests
// =============================================================================

use simple_compiler::mir::{
    is_async, nogc, nogc_singleton, pipeline_safe, AsyncEffect, BlockBuilder, BuiltinFunc, CallTarget, Effect,
    EffectSet, LocalKind, MirBlock, MirFunction, MirLocal, MirModule, NogcInstr, Terminator,
};

/// Test LocalKind enum
#[test]
fn test_local_kind_integration() {
    assert!(LocalKind::Parameter.is_parameter());
    assert!(!LocalKind::Parameter.is_local());
    assert!(!LocalKind::Local.is_parameter());
    assert!(LocalKind::Local.is_local());
}

/// Test AsyncEffect and is_async predicate
#[test]
fn test_async_effect_integration() {
    assert!(is_async(AsyncEffect::Compute));
    assert!(is_async(AsyncEffect::Io));
    assert!(!is_async(AsyncEffect::Wait));
}

/// Test pipeline_safe predicate
#[test]
fn test_pipeline_safe_integration() {
    assert!(pipeline_safe(&[]));
    assert!(pipeline_safe(&[AsyncEffect::Compute]));
    assert!(pipeline_safe(&[AsyncEffect::Io]));
    assert!(pipeline_safe(&[AsyncEffect::Compute, AsyncEffect::Io]));
    assert!(!pipeline_safe(&[AsyncEffect::Wait]));
    assert!(!pipeline_safe(&[AsyncEffect::Compute, AsyncEffect::Wait]));
}

/// Test NogcInstr enum
#[test]
fn test_nogc_instr_integration() {
    let const_instr = NogcInstr::Const(42);
    let add_instr = NogcInstr::Add;
    let gc_instr = NogcInstr::GcAlloc;

    assert!(nogc_singleton(&const_instr));
    assert!(nogc_singleton(&add_instr));
    assert!(!nogc_singleton(&gc_instr));
}

/// Test nogc predicate
#[test]
fn test_nogc_predicate_integration() {
    assert!(nogc(&[]));
    assert!(nogc(&[NogcInstr::Const(1), NogcInstr::Add]));
    assert!(!nogc(&[NogcInstr::GcAlloc]));
    assert!(!nogc(&[NogcInstr::Const(1), NogcInstr::GcAlloc]));
}

/// Test Effect enum
#[test]
fn test_effect_enum_integration() {
    assert!(Effect::Compute.is_async());
    assert!(Effect::Io.is_async());
    assert!(!Effect::Wait.is_async());
    assert!(Effect::GcAlloc.is_async());

    assert!(Effect::Compute.is_nogc());
    assert!(Effect::Io.is_nogc());
    assert!(Effect::Wait.is_nogc());
    assert!(!Effect::GcAlloc.is_nogc());
}

/// Test Effect to_async conversion
#[test]
fn test_effect_to_async_integration() {
    assert_eq!(Effect::Compute.to_async(), AsyncEffect::Compute);
    assert_eq!(Effect::Io.to_async(), AsyncEffect::Io);
    assert_eq!(Effect::Wait.to_async(), AsyncEffect::Wait);
    // GcAlloc maps to Compute for async model
    assert_eq!(Effect::GcAlloc.to_async(), AsyncEffect::Compute);
}

/// Test EffectSet
#[test]
fn test_effect_set_integration() {
    let mut set = EffectSet::new();
    assert!(set.is_pipeline_safe());
    assert!(set.is_nogc());

    set.push(Effect::Compute);
    assert!(set.is_pipeline_safe());

    set.push(Effect::Io);
    assert!(set.is_pipeline_safe());

    set.push(Effect::Wait);
    assert!(!set.is_pipeline_safe());

    let mut gc_set = EffectSet::new();
    gc_set.push(Effect::GcAlloc);
    assert!(!gc_set.is_nogc());
}

/// Test Terminator variants
#[test]
fn test_terminator_integration() {
    use simple_compiler::mir::VReg;

    let ret = Terminator::Return(None);
    let ret_val = Terminator::Return(Some(VReg(0)));
    let jump = Terminator::Jump(simple_compiler::mir::BlockId(0));

    assert!(matches!(ret, Terminator::Return(None)));
    assert!(matches!(ret_val, Terminator::Return(Some(_))));
    assert!(matches!(jump, Terminator::Jump(_)));

    // Test is_sealed and is_branching
    assert!(ret.is_sealed());
    assert!(!ret.is_branching());
    assert!(jump.is_branching());
}

/// Test BuiltinFunc enum
#[test]
fn test_builtin_func_integration() {
    // Test a few builtin functions
    let print_fn = BuiltinFunc::Print;
    let await_fn = BuiltinFunc::Await;
    let gc_alloc_fn = BuiltinFunc::GcAlloc;

    // Test effect() method
    assert_eq!(print_fn.effect(), Effect::Io);
    assert_eq!(await_fn.effect(), Effect::Wait);
    assert_eq!(gc_alloc_fn.effect(), Effect::GcAlloc);

    // Test from_name
    assert_eq!(BuiltinFunc::from_name("print"), Some(BuiltinFunc::Print));
    assert_eq!(BuiltinFunc::from_name("await"), Some(BuiltinFunc::Await));
    assert_eq!(BuiltinFunc::from_name("unknown"), None);

    // Test name()
    assert_eq!(print_fn.name(), "print");
}

/// Test CallTarget enum
#[test]
fn test_call_target_integration() {
    let pure_target = CallTarget::Pure("my_func".to_string());
    let io_target = CallTarget::Io("print".to_string());
    let blocking_target = CallTarget::Blocking("wait".to_string());
    let gc_target = CallTarget::GcAllocating("gc_new".to_string());

    // Test effect() method
    assert_eq!(pure_target.effect(), Effect::Compute);
    assert_eq!(io_target.effect(), Effect::Io);
    assert_eq!(blocking_target.effect(), Effect::Wait);
    assert_eq!(gc_target.effect(), Effect::GcAlloc);

    // Test is_async and is_nogc
    assert!(pure_target.is_async());
    assert!(pure_target.is_nogc());
    assert!(!blocking_target.is_async());
    assert!(!gc_target.is_nogc());

    // Test from_name
    let from_print = CallTarget::from_name("print");
    assert!(matches!(from_print, CallTarget::Io(_)));
}

/// Test BlockBuilder with BlockBuildState
#[test]
fn test_block_builder_state_integration() {
    use simple_compiler::mir::{BlockBuildState, BlockBuilder as MirBlockBuilder, BlockId};

    let block_id = BlockId(0);
    let mut builder = MirBlockBuilder::new(block_id);

    // Initially open
    assert!(builder.is_open());
    assert!(!builder.is_sealed());
    assert_eq!(builder.id(), block_id);

    // Seal with a terminator
    let seal_result = builder.seal(Terminator::Return(None));
    assert!(seal_result.is_ok());
    assert!(builder.is_sealed());
    assert!(!builder.is_open());

    // Can't seal again
    let reseal_result = builder.seal(Terminator::Unreachable);
    assert!(reseal_result.is_err());
}
