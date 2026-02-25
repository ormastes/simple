// Collection and string compilation for codegen.
// This file is included by instr.rs.

/// Helper to create a string literal in stack slot and get ptr/len
fn create_stack_string(
    builder: &mut FunctionBuilder,
    value: &str,
) -> (cranelift_codegen::ir::Value, cranelift_codegen::ir::Value) {
    let bytes = value.as_bytes();
    let len = bytes.len();

    let slot = builder.create_sized_stack_slot(
        cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            len as u32,
            0,
        ),
    );

    for (i, &byte) in bytes.iter().enumerate() {
        let byte_val = builder.ins().iconst(types::I8, byte as i64);
        builder.ins().stack_store(byte_val, slot, i as i32);
    }

    let ptr = builder.ins().stack_addr(types::I64, slot, 0);
    let len_val = builder.ins().iconst(types::I64, len as i64);
    (ptr, len_val)
}

/// Specification for building a collection literal
struct CollectionSpec {
    /// Runtime function to create the collection (e.g., "rt_array_new")
    create_fn: &'static str,
    /// Runtime function to add elements (e.g., "rt_array_push" or "rt_tuple_set")
    add_fn: &'static str,
    /// Whether add_fn needs an index argument (tuple_set needs index, array_push doesn't)
    needs_index: bool,
}

const ARRAY_SPEC: CollectionSpec = CollectionSpec {
    create_fn: "rt_array_new",
    add_fn: "rt_array_push",
    needs_index: false,
};

const TUPLE_SPEC: CollectionSpec = CollectionSpec {
    create_fn: "rt_tuple_new",
    add_fn: "rt_tuple_set",
    needs_index: true,
};

/// Compile a collection literal (array or tuple) using the given spec
fn compile_collection_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
    spec: &CollectionSpec,
) {
    // Create the collection
    let create_id = ctx.runtime_funcs[spec.create_fn];
    let create_ref = ctx.module.declare_func_in_func(create_id, builder.func);
    let size = builder.ins().iconst(types::I64, elements.len() as i64);
    let call = builder.ins().call(create_ref, &[size]);
    let collection = builder.inst_results(call)[0];

    // Get add function and value wrapper
    let add_id = ctx.runtime_funcs[spec.add_fn];
    let add_ref = ctx.module.declare_func_in_func(add_id, builder.func);
    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);

    // Add each element
    for (i, elem) in elements.iter().enumerate() {
        let elem_val = ctx.vreg_values[elem];
        let wrap_call = builder.ins().call(value_int_ref, &[elem_val]);
        let wrapped = builder.inst_results(wrap_call)[0];

        if spec.needs_index {
            let idx = builder.ins().iconst(types::I64, i as i64);
            builder.ins().call(add_ref, &[collection, idx, wrapped]);
        } else {
            builder.ins().call(add_ref, &[collection, wrapped]);
        }
    }

    ctx.vreg_values.insert(dest, collection);
}

fn compile_array_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
) {
    compile_collection_lit(ctx, builder, dest, elements, &ARRAY_SPEC);
}

fn compile_tuple_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
) {
    compile_collection_lit(ctx, builder, dest, elements, &TUPLE_SPEC);
}

fn compile_dict_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    keys: &[VReg],
    values: &[VReg],
) {
    let dict_new_id = ctx.runtime_funcs["rt_dict_new"];
    let dict_new_ref = ctx.module.declare_func_in_func(dict_new_id, builder.func);
    let capacity = builder.ins().iconst(types::I64, (keys.len() * 2) as i64);
    let call = builder.ins().call(dict_new_ref, &[capacity]);
    let dict = builder.inst_results(call)[0];

    let dict_set_id = ctx.runtime_funcs["rt_dict_set"];
    let dict_set_ref = ctx.module.declare_func_in_func(dict_set_id, builder.func);
    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);

    for (key, val) in keys.iter().zip(values.iter()) {
        let key_val = ctx.vreg_values[key];
        let val_val = ctx.vreg_values[val];
        let wrap_key = builder.ins().call(value_int_ref, &[key_val]);
        let wrapped_key = builder.inst_results(wrap_key)[0];
        let wrap_val = builder.ins().call(value_int_ref, &[val_val]);
        let wrapped_val = builder.inst_results(wrap_val)[0];
        builder.ins().call(dict_set_ref, &[dict, wrapped_key, wrapped_val]);
    }
    ctx.vreg_values.insert(dest, dict);
}

fn compile_index_get<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    collection: VReg,
    index: VReg,
) {
    let index_get_id = ctx.runtime_funcs["rt_index_get"];
    let index_get_ref = ctx.module.declare_func_in_func(index_get_id, builder.func);
    let coll_val = ctx.vreg_values[&collection];
    let idx_val = ctx.vreg_values[&index];

    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);
    let wrap_call = builder.ins().call(value_int_ref, &[idx_val]);
    let wrapped_idx = builder.inst_results(wrap_call)[0];

    let call = builder.ins().call(index_get_ref, &[coll_val, wrapped_idx]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_index_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    collection: VReg,
    index: VReg,
    value: VReg,
) {
    let index_set_id = ctx.runtime_funcs["rt_index_set"];
    let index_set_ref = ctx.module.declare_func_in_func(index_set_id, builder.func);
    let coll_val = ctx.vreg_values[&collection];
    let idx_val = ctx.vreg_values[&index];
    let val = ctx.vreg_values[&value];

    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);
    let wrap_idx = builder.ins().call(value_int_ref, &[idx_val]);
    let wrapped_idx = builder.inst_results(wrap_idx)[0];
    let wrap_val = builder.ins().call(value_int_ref, &[val]);
    let wrapped_val = builder.inst_results(wrap_val)[0];

    builder.ins().call(index_set_ref, &[coll_val, wrapped_idx, wrapped_val]);
}

fn compile_slice_op<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    collection: VReg,
    start: Option<VReg>,
    end: Option<VReg>,
    step: Option<VReg>,
) {
    let slice_id = ctx.runtime_funcs["rt_slice"];
    let slice_ref = ctx.module.declare_func_in_func(slice_id, builder.func);
    let coll_val = ctx.vreg_values[&collection];

    let start_val = start
        .map(|s| ctx.vreg_values[&s])
        .unwrap_or_else(|| builder.ins().iconst(types::I64, 0));
    let end_val = end
        .map(|e| ctx.vreg_values[&e])
        .unwrap_or_else(|| builder.ins().iconst(types::I64, i64::MAX));
    let step_val = step
        .map(|s| ctx.vreg_values[&s])
        .unwrap_or_else(|| builder.ins().iconst(types::I64, 1));

    let call = builder.ins().call(slice_ref, &[coll_val, start_val, end_val, step_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_const_string<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: &str,
) {
    let string_new_id = ctx.runtime_funcs["rt_string_new"];
    let string_new_ref = ctx.module.declare_func_in_func(string_new_id, builder.func);

    let (ptr, len_val) = if value.is_empty() {
        (builder.ins().iconst(types::I64, 0), builder.ins().iconst(types::I64, 0))
    } else {
        create_stack_string(builder, value)
    };

    let call = builder.ins().call(string_new_ref, &[ptr, len_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

fn compile_fstring_format<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    parts: &[FStringPart],
) {
    let string_new_id = ctx.runtime_funcs["rt_string_new"];
    let string_new_ref = ctx.module.declare_func_in_func(string_new_id, builder.func);
    let string_concat_id = ctx.runtime_funcs["rt_string_concat"];
    let string_concat_ref = ctx.module.declare_func_in_func(string_concat_id, builder.func);

    let null_ptr = builder.ins().iconst(types::I64, 0);
    let zero_len = builder.ins().iconst(types::I64, 0);
    let empty_call = builder.ins().call(string_new_ref, &[null_ptr, zero_len]);
    let mut result = builder.inst_results(empty_call)[0];

    for part in parts {
        let part_str = match part {
            FStringPart::Literal(s) => {
                if s.is_empty() {
                    continue;
                }
                let (ptr, len_val) = create_stack_string(builder, s);
                let call = builder.ins().call(string_new_ref, &[ptr, len_val]);
                builder.inst_results(call)[0]
            }
            FStringPart::Expr(vreg) => ctx.vreg_values[vreg],
        };

        let concat_call = builder.ins().call(string_concat_ref, &[result, part_str]);
        result = builder.inst_results(concat_call)[0];
    }

    ctx.vreg_values.insert(dest, result);
}
