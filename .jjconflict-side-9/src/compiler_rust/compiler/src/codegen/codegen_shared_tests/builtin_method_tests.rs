use super::*;

// Branch coverage: BuiltinMethod (compile_builtin_method in methods.rs)
// All (receiver_type, method) match arms
// =============================================================================

// --- Array methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_array_get, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "get".to_string(),
        args: vec![idx],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_set, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "set".to_string(),
        args: vec![idx, val],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_clear, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "clear".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_contains, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 1 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "contains".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_one_arg, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "slice".to_string(),
        args: vec![start],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_two_args, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 5 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "slice".to_string(),
        args: vec![start, end],
    });
    dest
});

cranelift_only_test!(shared_builtin_array_slice_three_args, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let step = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: step, value: 2 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "Array".to_string(),
        method: "slice".to_string(),
        args: vec![start, end, step],
    });
    dest
});

// --- String methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_string_len, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_concat, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "concat".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_starts_with, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "starts_with".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_ends_with, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "ends_with".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_contains, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "contains".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_slice, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "String".to_string(),
        method: "slice".to_string(),
        args: vec![start],
    });
    dest
});

// --- Dict methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_dict_get, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let key = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: key, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "get".to_string(),
        args: vec![key],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_set, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let key = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: key, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "set".to_string(),
        args: vec![key, val],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_len, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_clear, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "clear".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_keys, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "keys".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_values, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "values".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_contains, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "Dict".to_string(),
        method: "contains".to_string(),
        args: vec![arg],
    });
    dest
});

// --- Tuple methods via BuiltinMethod ---

cranelift_only_test!(shared_builtin_tuple_get, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let idx = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: t,
        receiver_type: "Tuple".to_string(),
        method: "get".to_string(),
        args: vec![idx],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_len, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: t,
        receiver_type: "Tuple".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_set, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let idx = f.new_vreg();
    let val = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: t,
        receiver_type: "Tuple".to_string(),
        method: "set".to_string(),
        args: vec![idx, val],
    });
    dest
});

// --- Unknown method (fallback to rt_method_not_found) ---

cranelift_only_test!(shared_builtin_unknown_method, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: recv,
        receiver_type: "Widget".to_string(),
        method: "frobnicate".to_string(),
        args: vec![],
    });
    dest
});

// --- BuiltinMethod with no dest (result discarded) ---

cranelift_only_test!(shared_builtin_no_dest, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let ret = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: None,
        receiver: recv,
        receiver_type: "Array".to_string(),
        method: "clear".to_string(),
        args: vec![],
    });
    block.instructions.push(MirInst::ConstInt { dest: ret, value: 0 });
    ret
});

// --- lowercase receiver_type variants ---

cranelift_only_test!(shared_builtin_array_lowercase, |f: &mut MirFunction| {
    let arr = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: arr, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: arr,
        receiver_type: "array".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_string_lowercase, |f: &mut MirFunction| {
    let s = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: s, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: s,
        receiver_type: "string".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_dict_lowercase, |f: &mut MirFunction| {
    let d = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: d, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: d,
        receiver_type: "dict".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_builtin_tuple_lowercase, |f: &mut MirFunction| {
    let t = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: t, value: 0 });
    block.instructions.push(MirInst::BuiltinMethod {
        dest: Some(dest),
        receiver: t,
        receiver_type: "tuple".to_string(),
        method: "len".to_string(),
        args: vec![],
    });
    dest
});

// =============================================================================
// Branch coverage: Cast instruction — float conversion branches
