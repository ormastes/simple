use super::*;

// Branch coverage: MethodCallStatic builtin method branches
// (try_compile_builtin_method_call in closures_structs.rs)
// =============================================================================

// --- slice/substring with various arg counts ---

cranelift_only_test!(shared_method_static_slice_no_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "slice".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_one_arg, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 1 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "slice".to_string(),
        args: vec![start],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_two_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 1 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 5 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "slice".to_string(),
        args: vec![start, end],
    });
    dest
});

cranelift_only_test!(shared_method_static_slice_three_args, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let end = f.new_vreg();
    let step = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: end, value: 10 });
    block.instructions.push(MirInst::ConstInt { dest: step, value: 2 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "slice".to_string(),
        args: vec![start, end, step],
    });
    dest
});

cranelift_only_test!(shared_method_static_substring, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let start = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "substring".to_string(),
        args: vec![start],
    });
    dest
});

// --- is_empty ---

cranelift_only_test!(shared_method_static_is_empty, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "is_empty".to_string(),
        args: vec![],
    });
    dest
});

// --- String methods ---

cranelift_only_test!(shared_method_static_starts_with, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "starts_with".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_ends_with, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "ends_with".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_concat, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "concat".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_contains, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "contains".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_char_at, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "char_at".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_at, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "at".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_trim, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "trim".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_split, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "split".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_replace, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let a = f.new_vreg();
    let b = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: b, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "replace".to_string(),
        args: vec![a, b],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_upper, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "to_upper".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_upper, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "upper".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_lower, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "to_lower".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_lower, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "lower".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_int, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "to_int".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_i64, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "to_i64".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_parse_int, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "parse_int".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_to_string, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "to_string".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_str, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "str".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_join, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "join".to_string(),
        args: vec![arg],
    });
    dest
});

// --- Array methods ---

cranelift_only_test!(shared_method_static_push, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 42 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "push".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_pop, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "pop".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_clear, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "clear".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_map, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "map".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_filter, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "filter".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_sort, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "sort".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_reverse, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "reverse".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_first, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "first".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_last, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "last".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_find, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "find".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_any, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "any".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_all, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "all".to_string(),
        args: vec![arg],
    });
    dest
});

// --- Result/Option methods (special branches) ---

cranelift_only_test!(shared_method_static_unwrap, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "unwrap".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_unwrap_or, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let arg = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::ConstInt { dest: arg, value: 99 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "unwrap_or".to_string(),
        args: vec![arg],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_none, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "is_none".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_some, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "is_some".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_ok, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "is_ok".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_is_err, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "is_err".to_string(),
        args: vec![],
    });
    dest
});

// --- Dict methods ---

cranelift_only_test!(shared_method_static_keys, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "keys".to_string(),
        args: vec![],
    });
    dest
});

cranelift_only_test!(shared_method_static_values, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "values".to_string(),
        args: vec![],
    });
    dest
});

// --- Qualified method name branch (rsplit('.')) ---

cranelift_only_test!(shared_method_static_qualified_len, |f: &mut MirFunction| {
    let recv = f.new_vreg();
    let dest = f.new_vreg();
    let block = f.block_mut(BlockId(0)).unwrap();
    block.instructions.push(MirInst::ConstInt { dest: recv, value: 0 });
    block.instructions.push(MirInst::MethodCallStatic {
        dest: Some(dest),
        receiver: recv,
        func_name: "text.len".to_string(),
        args: vec![],
    });
    dest
});

// =============================================================================
