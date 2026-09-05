use super::{aot_compiles, aot_compiles_module};
use crate::codegen::jit::JitCompiler;
use crate::hir::TypeId;
use crate::mir::{BlockId, CallTarget, LocalKind, MirFunction, MirInst, MirLocal, MirModule, Terminator};
use simple_parser::ast::Visibility;

// =============================================================================
// Memory (memory.rs) — LocalAddr, Load, Store
// =============================================================================

#[test]
fn codegen_local_addr_store_load() {
    assert!(aot_compiles("local_mem", |f| {
        f.locals.push(MirLocal {
            name: "x".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        let addr = f.new_vreg();
        let val = f.new_vreg();
        let loaded = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::LocalAddr {
            dest: addr,
            local_index: 0,
        });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Store {
            addr,
            value: val,
            ty: TypeId::I64,
        });
        block.instructions.push(MirInst::Load {
            dest: loaded,
            addr,
            ty: TypeId::I64,
        });
        loaded
    }));
}

// =============================================================================
// Boxing (inline in compile_instruction)
// =============================================================================

#[test]
fn codegen_box_unbox_int() {
    assert!(aot_compiles("box_int", |f| {
        let val = f.new_vreg();
        let boxed = f.new_vreg();
        let unboxed = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::BoxInt {
            dest: boxed,
            value: val,
        });
        block.instructions.push(MirInst::UnboxInt {
            dest: unboxed,
            value: boxed,
        });
        unboxed
    }));
}

#[test]
fn codegen_box_unbox_float() {
    assert!(aot_compiles("box_float", |f| {
        let fval = f.new_vreg();
        let boxed = f.new_vreg();
        let unboxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat { dest: fval, value: 7.0 });
        block.instructions.push(MirInst::BoxFloat {
            dest: boxed,
            value: fval,
        });
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: boxed,
        });
        block.instructions.push(MirInst::Cast {
            dest,
            source: unboxed,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
}

#[test]
fn codegen_unbox_float_accepts_already_unboxed_f32() {
    assert!(aot_compiles("unbox_raw_f32", |f| {
        let f64_value = f.new_vreg();
        let f32_value = f.new_vreg();
        let unboxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat {
            dest: f64_value,
            value: 7.0,
        });
        block.instructions.push(MirInst::Cast {
            dest: f32_value,
            source: f64_value,
            from_ty: TypeId::F64,
            to_ty: TypeId::F32,
        });
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: f32_value,
        });
        block.instructions.push(MirInst::Cast {
            dest,
            source: unboxed,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
}

#[test]
fn codegen_unbox_float_accepts_raw_f64_and_tagged_nil() {
    assert!(aot_compiles("unbox_raw_f64", |f| {
        let raw = f.new_vreg();
        let unboxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat {
            dest: raw,
            value: f64::from_bits(3),
        });
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: raw,
        });
        block.instructions.push(MirInst::Cast {
            dest,
            source: unboxed,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
    assert!(aot_compiles("unbox_tagged_nil", |f| {
        let tagged_nil = f.new_vreg();
        let unboxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt {
            dest: tagged_nil,
            value: 3,
        });
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: tagged_nil,
        });
        block.instructions.push(MirInst::Cast {
            dest,
            source: unboxed,
            from_ty: TypeId::F64,
            to_ty: TypeId::I64,
        });
        dest
    }));
}

#[test]
fn tagged_float_and_nil_runtime_semantics_match_unbox_float_contract() {
    use simple_runtime::value::{rt_value_as_float, rt_value_float, RuntimeValue};

    let tagged_float = rt_value_float(7.25);
    assert_eq!(rt_value_as_float(tagged_float), 7.25);

    let tagged_nil = RuntimeValue::NIL;
    assert_eq!(tagged_nil.to_raw(), 3);
    assert_eq!(rt_value_as_float(tagged_nil), 0.0);
    let nil_result = if tagged_nil.to_raw() == 3 {
        f64::from_bits(3)
    } else {
        rt_value_as_float(tagged_nil)
    };
    assert_eq!(nil_result.to_bits(), 3);

    let raw_f64 = f64::from_bits(3);
    assert_eq!(raw_f64.to_bits(), 3);
}

#[test]
fn jit_unbox_float_preserves_cross_block_provenance_and_results() {
    fn probe(name: &str, source: impl FnOnce(&mut MirFunction) -> crate::mir::VReg) -> MirFunction {
        let mut f = MirFunction::new(name.to_string(), TypeId::I64, Visibility::Public);
        let source_value = source(&mut f);
        let decode_block = f.new_block();
        f.block_mut(BlockId(0)).unwrap().terminator = Terminator::Jump(decode_block);

        let unboxed = f.new_vreg();
        let result_bits = f.new_vreg();
        let block = f.block_mut(decode_block).unwrap();
        block.instructions.push(MirInst::UnboxFloat {
            dest: unboxed,
            value: source_value,
        });
        block.instructions.push(MirInst::Call {
            dest: Some(result_bits),
            target: CallTarget::from_name("spl_f64_to_bits"),
            args: vec![unboxed],
        });
        block.terminator = Terminator::Return(Some(result_bits));
        f
    }

    let mut module = MirModule::new();
    module.functions.push(probe("raw_sentinel_bits", |f| {
        let value = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstFloat {
            dest: value,
            value: f64::from_bits(3),
        });
        value
    }));
    module.functions.push(probe("raw_ordinary", |f| {
        let value = f.new_vreg();
        f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::ConstFloat {
            dest: value,
            value: 7.25,
        });
        value
    }));
    module.functions.push(probe("tagged_float", |f| {
        let raw = f.new_vreg();
        let boxed = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstFloat { dest: raw, value: 7.25 });
        block.instructions.push(MirInst::BoxFloat {
            dest: boxed,
            value: raw,
        });
        boxed
    }));
    module.functions.push(probe("tagged_nil", |f| {
        let value = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: value, value: 3 });
        value
    }));

    let mut jit = JitCompiler::new_static().expect("JIT creation");
    jit.compile_module(&module).expect("JIT compilation");
    unsafe {
        assert_eq!(jit.call_i64_void("raw_sentinel_bits").unwrap() as u64, 3);
        assert_eq!(jit.call_i64_void("raw_ordinary").unwrap() as u64, 7.25f64.to_bits());
        assert_eq!(jit.call_i64_void("tagged_float").unwrap() as u64, 7.25f64.to_bits());
        assert_eq!(jit.call_i64_void("tagged_nil").unwrap() as u64, 3);
    }
}

// =============================================================================
// Drop / EndScope (no-ops in codegen)
// =============================================================================

#[test]
fn codegen_drop_noop() {
    assert!(aot_compiles("drop_noop", |f| {
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::Drop {
            value: val,
            ty: TypeId::I64,
        });
        val
    }));
}

#[test]
fn codegen_end_scope_noop() {
    assert!(aot_compiles("end_scope", |f| {
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::EndScope { local_index: 0 });
        val
    }));
}

// =============================================================================
// GcAlloc / Wait / GetElementPtr (memory.rs)
// =============================================================================

#[test]
fn codegen_gc_alloc() {
    assert!(aot_compiles("gc_alloc", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::GcAlloc { dest, ty: TypeId::I64 });
        dest
    }));
}

#[test]
fn codegen_wait() {
    assert!(aot_compiles("wait_test", |f| {
        let target = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: target, value: 0 });
        block.instructions.push(MirInst::Wait {
            dest: Some(dest),
            target,
        });
        dest
    }));
}

#[test]
fn codegen_get_element_ptr() {
    assert!(aot_compiles("gep", |f| {
        let base = f.new_vreg();
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: base, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block
            .instructions
            .push(MirInst::GetElementPtr { dest, base, index: idx });
        dest
    }));
}

// =============================================================================
// Global Load/Store (memory.rs)
// =============================================================================

#[test]
fn codegen_global_load_store() {
    let mut func = MirFunction::new(
        "global_test".to_string(),
        TypeId::I64,
        simple_parser::ast::Visibility::Public,
    );
    let val = func.new_vreg();
    let loaded = func.new_vreg();
    let block = func.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::GlobalStore {
        global_name: "MY_GLOBAL".to_string(),
        value: val,
        ty: TypeId::I64,
    });
    block.instructions.push(MirInst::GlobalLoad {
        dest: loaded,
        global_name: "MY_GLOBAL".to_string(),
        ty: TypeId::I64,
    });
    block.terminator = crate::mir::Terminator::Return(Some(loaded));

    let mut module = MirModule::new();
    module.globals.push(("MY_GLOBAL".to_string(), TypeId::I64, true));
    module.functions.push(func);

    assert!(aot_compiles_module(module));
}
