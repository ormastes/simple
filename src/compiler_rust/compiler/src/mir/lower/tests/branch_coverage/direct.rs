//! Direct MIR construction tests for MIR lowering
//!
//! These variants are NOT emitted by the current lowerer. To achieve 100%
//! branch coverage we construct MIR directly and verify each instruction
//! round-trips correctly through MirFunction.

use super::helpers::*;
use crate::hir;
use crate::mir::{self, MirInst};
use crate::mir::function::MirFunction;

// --- Copy ---

#[test]
fn direct_copy() {
    let func = build_mir_func("copy_test", |f| {
        let src = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::Copy { dest, src });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::Copy { .. })));
}

// --- GlobalStore ---

#[test]
fn direct_global_store() {
    let func = build_mir_func("global_store_test", |f| {
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::GlobalStore {
            global_name: "MY_GLOBAL".to_string(),
            value,
            ty: hir::TypeId::I64,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::GlobalStore { .. })));
}

// --- GcAlloc ---

#[test]
fn direct_gc_alloc() {
    let func = build_mir_func("gc_alloc_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::GcAlloc {
            dest,
            ty: hir::TypeId::I64,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::GcAlloc { .. })));
}

// --- Wait ---

#[test]
fn direct_wait() {
    let func = build_mir_func("wait_test", |f| {
        let dest = f.new_vreg();
        let target = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::Wait {
            dest: Some(dest),
            target,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::Wait { .. })));
}

// --- InterpCall ---

#[test]
fn direct_interp_call() {
    let func = build_mir_func("interp_call_test", |f| {
        let dest = f.new_vreg();
        let arg = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::InterpCall {
            dest: Some(dest),
            func_name: "test_func".to_string(),
            args: vec![arg],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::InterpCall { .. })));
}

// --- InterpEval ---

#[test]
fn direct_interp_eval() {
    let func = build_mir_func("interp_eval_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::InterpEval { dest, expr_index: 0 });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::InterpEval { .. })));
}

// --- IndexSet ---

#[test]
fn direct_index_set() {
    let func = build_mir_func("index_set_test", |f| {
        let collection = f.new_vreg();
        let index = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::IndexSet {
            collection,
            index,
            value,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::IndexSet { .. })));
}

// --- SliceOp ---

#[test]
fn direct_slice_op() {
    let func = build_mir_func("slice_op_test", |f| {
        let dest = f.new_vreg();
        let collection = f.new_vreg();
        let start = f.new_vreg();
        let end = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::SliceOp {
            dest,
            collection,
            start: Some(start),
            end: Some(end),
            step: None,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::SliceOp { .. })));
}

// --- Spread ---

#[test]
fn direct_spread() {
    let func = build_mir_func("spread_test", |f| {
        let dest = f.new_vreg();
        let source = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::Spread { dest, source });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::Spread { .. })));
}

// --- ConstSymbol ---

#[test]
fn direct_const_symbol() {
    let func = build_mir_func("const_symbol_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstSymbol {
            dest,
            value: "my_symbol".to_string(),
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ConstSymbol { .. })));
}

// --- FStringFormat ---

#[test]
fn direct_fstring_format() {
    use crate::mir::FStringPart;
    let func = build_mir_func("fstring_test", |f| {
        let dest = f.new_vreg();
        let expr_reg = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::FStringFormat {
            dest,
            parts: vec![
                FStringPart::Literal("Hello, ".to_string()),
                FStringPart::Expr(expr_reg),
                FStringPart::Literal("!".to_string()),
            ],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::FStringFormat { .. })));
}

// --- MethodCallVirtual ---

#[test]
fn direct_method_call_virtual() {
    let func = build_mir_func("virtual_call_test", |f| {
        let dest = f.new_vreg();
        let receiver = f.new_vreg();
        let arg = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::MethodCallVirtual {
            dest: Some(dest),
            receiver,
            vtable_slot: 0,
            param_types: vec![hir::TypeId::I64],
            return_type: hir::TypeId::I64,
            args: vec![arg],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::MethodCallVirtual { .. })));
}

// --- BuiltinMethod ---

#[test]
fn direct_builtin_method() {
    let func = build_mir_func("builtin_method_test", |f| {
        let dest = f.new_vreg();
        let receiver = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::BuiltinMethod {
            dest: Some(dest),
            receiver,
            receiver_type: "Array".to_string(),
            method: "len".to_string(),
            args: vec![],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::BuiltinMethod { .. })));
}

// --- ExternMethodCall ---

#[test]
fn direct_extern_method_call() {
    let func = build_mir_func("extern_method_test", |f| {
        let dest = f.new_vreg();
        let receiver = f.new_vreg();
        let arg = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ExternMethodCall {
            dest: Some(dest),
            receiver: Some(receiver),
            class_name: "HttpClient".to_string(),
            method_name: "get".to_string(),
            is_static: false,
            args: vec![arg],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ExternMethodCall { .. })));
}

// --- PatternTest ---

#[test]
fn direct_pattern_test() {
    use crate::mir::{MirLiteral, MirPattern};
    let func = build_mir_func("pattern_test", |f| {
        let dest = f.new_vreg();
        let subject = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::PatternTest {
            dest,
            subject,
            pattern: MirPattern::Literal(MirLiteral::Int(42)),
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::PatternTest { .. })));
}

// --- PatternBind ---

#[test]
fn direct_pattern_bind() {
    use crate::mir::PatternBinding;
    let func = build_mir_func("pattern_bind_test", |f| {
        let dest = f.new_vreg();
        let subject = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::PatternBind {
            dest,
            subject,
            binding: PatternBinding {
                name: "x".to_string(),
                path: vec![],
            },
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::PatternBind { .. })));
}

// --- EnumDiscriminant ---

#[test]
fn direct_enum_discriminant() {
    let func = build_mir_func("enum_disc_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::EnumDiscriminant { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::EnumDiscriminant { .. })));
}

// --- EnumPayload ---

#[test]
fn direct_enum_payload() {
    let func = build_mir_func("enum_payload_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::EnumPayload { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::EnumPayload { .. })));
}

// --- EnumWith ---

#[test]
fn direct_enum_with() {
    let func = build_mir_func("enum_with_test", |f| {
        let dest = f.new_vreg();
        let payload = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::EnumWith {
            dest,
            enum_name: "Option".to_string(),
            variant_name: "Some".to_string(),
            payload,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::EnumWith { .. })));
}

// --- UnionDiscriminant ---

#[test]
fn direct_union_discriminant() {
    let func = build_mir_func("union_disc_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::UnionDiscriminant { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::UnionDiscriminant { .. })));
}

// --- UnionPayload ---

#[test]
fn direct_union_payload() {
    let func = build_mir_func("union_payload_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::UnionPayload {
            dest,
            value,
            type_index: 0,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::UnionPayload { .. })));
}

// --- FutureCreate ---

#[test]
fn direct_future_create() {
    let func = build_mir_func("future_test", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::FutureCreate { dest, body_block });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::FutureCreate { .. })));
}

// --- Await ---

#[test]
fn direct_await() {
    let func = build_mir_func("await_test", |f| {
        let dest = f.new_vreg();
        let future = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::Await { dest, future });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::Await { .. })));
}

// --- ActorSend ---

#[test]
fn direct_actor_send() {
    let func = build_mir_func("actor_send_test", |f| {
        let actor = f.new_vreg();
        let message = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ActorSend { actor, message });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ActorSend { .. })));
}

// --- ActorRecv ---

#[test]
fn direct_actor_recv() {
    let func = build_mir_func("actor_recv_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ActorRecv { dest });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ActorRecv { .. })));
}

// --- GeneratorCreate ---

#[test]
fn direct_generator_create() {
    let func = build_mir_func("gen_create_test", |f| {
        let dest = f.new_vreg();
        let body_block = f.new_block();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::GeneratorCreate { dest, body_block });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::GeneratorCreate { .. })));
}

// --- Yield ---

#[test]
fn direct_yield() {
    let func = build_mir_func("yield_test", |f| {
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::Yield { value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::Yield { .. })));
}

// --- GeneratorNext ---

#[test]
fn direct_generator_next() {
    let func = build_mir_func("gen_next_test", |f| {
        let dest = f.new_vreg();
        let generator = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::GeneratorNext { dest, generator });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::GeneratorNext { .. })));
}

// --- TryUnwrap ---

#[test]
fn direct_try_unwrap() {
    let func = build_mir_func("try_unwrap_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let error_dest = f.new_vreg();
        let error_block = f.new_block();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::TryUnwrap {
            dest,
            value,
            error_block,
            error_dest,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::TryUnwrap { .. })));
}

// --- OptionSome ---

#[test]
fn direct_option_some() {
    let func = build_mir_func("option_some_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::OptionSome { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::OptionSome { .. })));
}

// --- OptionNone ---

#[test]
fn direct_option_none() {
    let func = build_mir_func("option_none_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::OptionNone { dest });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::OptionNone { .. })));
}

// --- ResultOk ---

#[test]
fn direct_result_ok() {
    let func = build_mir_func("result_ok_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ResultOk { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ResultOk { .. })));
}

// --- ResultErr ---

#[test]
fn direct_result_err() {
    let func = build_mir_func("result_err_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ResultErr { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ResultErr { .. })));
}

// --- ContractOldCapture ---

#[test]
fn direct_contract_old_capture() {
    let func = build_mir_func("old_capture_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ContractOldCapture { dest, value });
    });
    assert!(func_has_inst(&func, |i| matches!(
        i,
        MirInst::ContractOldCapture { .. }
    )));
}

// --- UnitWiden ---

#[test]
fn direct_unit_widen() {
    let func = build_mir_func("unit_widen_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::UnitWiden {
            dest,
            value,
            from_bits: 8,
            to_bits: 16,
            signed: true,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::UnitWiden { .. })));
}

// --- UnitNarrow ---

#[test]
fn direct_unit_narrow() {
    use crate::mir::UnitOverflowBehavior;
    let func = build_mir_func("unit_narrow_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::UnitNarrow {
            dest,
            value,
            from_bits: 16,
            to_bits: 8,
            signed: true,
            overflow: UnitOverflowBehavior::Saturate,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::UnitNarrow { .. })));
}

// --- UnitSaturate ---

#[test]
fn direct_unit_saturate() {
    let func = build_mir_func("unit_saturate_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::UnitSaturate {
            dest,
            value,
            min: 0,
            max: 255,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::UnitSaturate { .. })));
}

// --- GpuSharedAlloc ---

#[test]
fn direct_gpu_shared_alloc() {
    let func = build_mir_func("gpu_shared_alloc_test", |f| {
        let dest = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::GpuSharedAlloc {
            dest,
            element_type: hir::TypeId::F64,
            size: 256,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::GpuSharedAlloc { .. })));
}

// --- ParMap ---

#[test]
fn direct_par_map() {
    let func = build_mir_func("par_map_test", |f| {
        let dest = f.new_vreg();
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ParMap {
            dest,
            input,
            closure,
            backend: None,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ParMap { .. })));
}

// --- ParReduce ---

#[test]
fn direct_par_reduce() {
    let func = build_mir_func("par_reduce_test", |f| {
        let dest = f.new_vreg();
        let input = f.new_vreg();
        let initial = f.new_vreg();
        let closure = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ParReduce {
            dest,
            input,
            initial,
            closure,
            backend: None,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ParReduce { .. })));
}

// --- ParFilter ---

#[test]
fn direct_par_filter() {
    let func = build_mir_func("par_filter_test", |f| {
        let dest = f.new_vreg();
        let input = f.new_vreg();
        let predicate = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ParFilter {
            dest,
            input,
            predicate,
            backend: None,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ParFilter { .. })));
}

// --- ParForEach ---

#[test]
fn direct_par_for_each() {
    let func = build_mir_func("par_for_each_test", |f| {
        let input = f.new_vreg();
        let closure = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::ParForEach {
            input,
            closure,
            backend: None,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::ParForEach { .. })));
}

// --- DictLit ---

#[test]
fn direct_dict_lit() {
    let func = build_mir_func("dict_lit_test", |f| {
        let dest = f.new_vreg();
        let key = f.new_vreg();
        let val = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::DictLit {
            dest,
            keys: vec![key],
            values: vec![val],
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::DictLit { .. })));
}

// --- FieldSet ---

#[test]
fn direct_field_set() {
    let func = build_mir_func("field_set_test", |f| {
        let object = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::FieldSet {
            object,
            byte_offset: 0,
            field_type: hir::TypeId::I64,
            value,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::FieldSet { .. })));
}

// --- PointerNew ---

#[test]
fn direct_pointer_new() {
    use crate::hir::PointerKind;
    let func = build_mir_func("pointer_new_test", |f| {
        let dest = f.new_vreg();
        let value = f.new_vreg();
        let block = f.block_mut(mir::BlockId(0)).unwrap();
        block.instructions.push(MirInst::PointerNew {
            dest,
            kind: PointerKind::Unique,
            value,
        });
    });
    assert!(func_has_inst(&func, |i| matches!(i, MirInst::PointerNew { .. })));
}
