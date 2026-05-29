use super::*;

// =============================================================================
// Phase 2: Collections
// =============================================================================

shared_test!(shared_array_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::ArrayLit {
        dest,
        elements: vec![a, b],
    });
    dest
});

shared_test!(shared_tuple_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::TupleLit {
        dest,
        elements: vec![a, b],
    });
    dest
});

shared_test!(shared_dict_lit, |f: &mut MirFunction| {
    let k = f.new_vreg();
    let v = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: k, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: v, value: 42 });
    block.instructions.push(MirInst::DictLit {
        dest,
        keys: vec![k],
        values: vec![v],
    });
    dest
});

shared_test!(shared_vec_lit, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::VecLit {
        dest,
        elements: vec![a],
    });
    dest
});

shared_test!(shared_index_get, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a],
    });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::IndexGet {
        dest,
        collection: arr,
        index: idx,
    });
    dest
});

shared_test!(shared_index_set, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a],
    });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::IndexSet {
        collection: arr,
        index: idx,
        value: val,
    });
    arr
});

shared_test!(shared_slice_op, |f: &mut MirFunction| {
    let a = f.new_vreg();
    let b = f.new_vreg();
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
    block.instructions.push(MirInst::ArrayLit {
        dest: arr,
        elements: vec![a, b],
    });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::SliceOp {
        dest,
        collection: arr,
        start: Some(start),
        end: None,
        step: None,
    });
    dest
});

// =============================================================================
// Phase 2: Structs / Fields
// =============================================================================

shared_test!(shared_struct_init_field_ops, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let obj = f.new_vreg();
    let got = f.new_vreg();
    let newval = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::StructInit {
        dest: obj,
        type_id: TypeId::I64,
        struct_size: 8,
        field_offsets: vec![0],
        field_types: vec![TypeId::I64],
        field_values: vec![val],
    });
    block.instructions.push(MirInst::FieldGet {
        dest: got,
        object: obj,
        byte_offset: 0,
        field_type: TypeId::I64,
    });
    block.instructions.push(MirInst::ConstInt {
        dest: newval,
        value: 99,
    });
    block.instructions.push(MirInst::FieldSet {
        object: obj,
        byte_offset: 0,
        field_type: TypeId::I64,
        value: newval,
    });
    got
});

// =============================================================================
// Phase 2: FString
// =============================================================================

shared_test!(shared_fstring_format, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let boxed = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BoxInt {
        dest: boxed,
        value: val,
    });
    block.instructions.push(MirInst::FStringFormat {
        dest,
        parts: vec![FStringPart::Literal("value=".to_string()), FStringPart::Expr(boxed)],
    });
    dest
});

// =============================================================================
// Phase 3: Enums / Unions
// =============================================================================

shared_test!(shared_enum_unit, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0)).unwrap().instructions.push(MirInst::EnumUnit {
        dest,
        enum_name: "Color".to_string(),
        variant_name: "Red".to_string(),
    });
    dest
});

shared_test!(shared_enum_with, |f: &mut MirFunction| {
    let payload = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt {
        dest: payload,
        value: 42,
    });
    block.instructions.push(MirInst::EnumWith {
        dest,
        enum_name: "Option".to_string(),
        variant_name: "Some".to_string(),
        payload,
    });
    dest
});

shared_test!(shared_enum_discriminant, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::EnumUnit {
        dest: val,
        enum_name: "Color".to_string(),
        variant_name: "Red".to_string(),
    });
    block.instructions.push(MirInst::EnumDiscriminant { dest, value: val });
    dest
});

shared_test!(shared_union_wrap, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::UnionWrap {
        dest,
        value: val,
        type_index: 0,
    });
    dest
});

// =============================================================================
// Phase 3: Option / Result
// =============================================================================

shared_test!(shared_option_some, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::OptionSome { dest, value: val });
    dest
});

shared_test!(shared_option_none, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::OptionNone { dest });
    dest
});

shared_test!(shared_result_ok, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::ResultOk { dest, value: val });
    dest
});

shared_test!(shared_result_err, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 1 });
    block.instructions.push(MirInst::ResultErr { dest, value: val });
    dest
});

// =============================================================================
// Phase 3: Pattern matching
// =============================================================================

shared_test!(shared_pattern_test, |f: &mut MirFunction| {
    let subject = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt {
        dest: subject,
        value: 42,
    });
    block.instructions.push(MirInst::PatternTest {
        dest,
        subject,
        pattern: MirPattern::Literal(MirLiteral::Int(42)),
    });
    dest
});

shared_test!(shared_pattern_bind, |f: &mut MirFunction| {
    let subject = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt {
        dest: subject,
        value: 42,
    });
    block.instructions.push(MirInst::PatternBind {
        dest,
        subject,
        binding: PatternBinding {
            name: "x".to_string(),
            path: vec![],
        },
    });
    dest
});

// =============================================================================
// Phase 3: Async / Actors / Generators
// =============================================================================

shared_test!(shared_future_create, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 42 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::FutureCreate { dest, body_block });
    dest
});

shared_test!(shared_await, |f: &mut MirFunction| {
    let future = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: future, value: 0 });
    block.instructions.push(MirInst::Await { dest, future });
    dest
});

shared_test!(shared_actor_spawn, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::ActorSpawn { dest, body_block });
    dest
});

shared_test!(shared_actor_send, |f: &mut MirFunction| {
    let actor = f.new_vreg();
    let msg = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: actor, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: msg, value: 42 });
    block.instructions.push(MirInst::ActorSend { actor, message: msg });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_generator_create, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    let body_block = f.new_block();
    let ret = f.new_vreg();
    f.block_mut(body_block)
        .unwrap()
        .instructions
        .push(MirInst::ConstInt { dest: ret, value: 0 });
    f.block_mut(body_block).unwrap().terminator = Terminator::Return(Some(ret));
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GeneratorCreate { dest, body_block });
    dest
});

shared_test!(shared_yield, |f: &mut MirFunction| {
    let val = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::Yield { value: val });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// =============================================================================
// Phase 3: GPU
// =============================================================================

shared_test!(shared_gpu_global_id, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuGlobalId { dest, dim: 0 });
    dest
});

shared_test!(shared_gpu_barrier, |f: &mut MirFunction| {
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::GpuBarrier);
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

shared_test!(shared_gpu_shared_alloc, |f: &mut MirFunction| {
    let dest = f.new_vreg();
    f.block_mut(BlockId(0))
        .unwrap()
        .instructions
        .push(MirInst::GpuSharedAlloc {
            dest,
            element_type: TypeId::F64,
            size: 64,
        });
    dest
});

// =============================================================================
// Phase 3: Parallel
// =============================================================================

shared_test!(shared_par_map, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let closure = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
    block.instructions.push(MirInst::ConstInt {
        dest: closure,
        value: 0,
    });
    block.instructions.push(MirInst::ParMap {
        dest,
        input,
        closure,
        backend: None,
    });
    dest
});

shared_test!(shared_par_for_each, |f: &mut MirFunction| {
    let input = f.new_vreg();
    let closure = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: input, value: 0 });
    block.instructions.push(MirInst::ConstInt {
        dest: closure,
        value: 0,
    });
    block.instructions.push(MirInst::ParForEach {
        input,
        closure,
        backend: None,
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});
