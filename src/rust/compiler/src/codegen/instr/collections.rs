// Collection and string compilation for codegen.

use cranelift_codegen::ir::{types, InstBuilder, MemFlags, StackSlotData, StackSlotKind};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::{FStringPart, VReg};

use super::helpers::get_vreg_or_default;
use super::{InstrContext, InstrResult};

/// Helper to create a string literal in stack slot and get ptr/len
pub(super) fn create_stack_string(
    builder: &mut FunctionBuilder,
    value: &str,
) -> (cranelift_codegen::ir::Value, cranelift_codegen::ir::Value) {
    let bytes = value.as_bytes();
    let len = bytes.len();

    let slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
        cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
        len as u32,
        0,
    ));

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
pub(super) fn compile_collection_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
    spec: &CollectionSpec,
) {
    // Create the collection
    // Use minimum capacity of 16 for arrays to allow push operations on empty arrays
    let create_id = ctx.runtime_funcs[spec.create_fn];
    let create_ref = ctx.module.declare_func_in_func(create_id, builder.func);
    let capacity = if elements.is_empty() && spec.create_fn == "rt_array_new" {
        16 // Default capacity for empty arrays to allow push
    } else {
        elements.len()
    };
    let size = builder.ins().iconst(types::I64, capacity as i64);
    let call = builder.ins().call(create_ref, &[size]);
    let collection = builder.inst_results(call)[0];

    // Get add function and value wrapper
    let add_id = ctx.runtime_funcs[spec.add_fn];
    let add_ref = ctx.module.declare_func_in_func(add_id, builder.func);
    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);

    // Add each element
    for (i, elem) in elements.iter().enumerate() {
        let elem_val = get_vreg_or_default(ctx, builder, elem);
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

pub(super) fn compile_array_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
) {
    compile_collection_lit(ctx, builder, dest, elements, &ARRAY_SPEC);
}

pub(super) fn compile_tuple_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
) {
    compile_collection_lit(ctx, builder, dest, elements, &TUPLE_SPEC);
}

/// Compile a SIMD vector literal
/// For now, we represent vectors as arrays. A full implementation would use
/// Cranelift's SIMD vector types for better performance.
pub(super) fn compile_vec_lit<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    elements: &[VReg],
) {
    // For now, use the same implementation as arrays
    // In a full SIMD implementation, we would use Cranelift's vector types
    compile_collection_lit(ctx, builder, dest, elements, &ARRAY_SPEC);
}

/// Compile a SIMD vector reduction operation (sum, product, min, max, all, any)
/// Takes a vector and reduces it to a scalar value using the specified runtime function.
pub(super) fn compile_vec_reduction<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    runtime_fn: &str,
) {
    let func_id = ctx.runtime_funcs[runtime_fn];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let source_val = get_vreg_or_default(ctx, builder, &source);
    let call = builder.ins().call(func_ref, &[source_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD lane extract: v[idx] -> element
pub(super) fn compile_vec_extract<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    vector: VReg,
    index: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_vec_extract"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let vector_val = get_vreg_or_default(ctx, builder, &vector);
    let index_val = get_vreg_or_default(ctx, builder, &index);
    let call = builder.ins().call(func_ref, &[vector_val, index_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD lane insert: v.with(idx, val) -> new vector
pub(super) fn compile_vec_with<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    vector: VReg,
    index: VReg,
    value: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_vec_with"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let vector_val = ctx.vreg_values[&vector];
    let index_val = ctx.vreg_values[&index];
    let value_val = ctx.vreg_values[&value];
    let call = builder.ins().call(func_ref, &[vector_val, index_val, value_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD element-wise math operation (sqrt, abs, floor, ceil, round)
/// Takes a vector and returns a vector with the operation applied to each element.
pub(super) fn compile_vec_math<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    runtime_fn: &str,
) {
    let func_id = ctx.runtime_funcs[runtime_fn];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let source_val = get_vreg_or_default(ctx, builder, &source);
    let call = builder.ins().call(func_ref, &[source_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD shuffle: reorder lanes within a single vector
/// v.shuffle([3, 2, 1, 0]) -> reordered vector
pub(super) fn compile_vec_shuffle<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    source: VReg,
    indices: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_vec_shuffle"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let source_val = ctx.vreg_values[&source];
    let indices_val = ctx.vreg_values[&indices];
    let call = builder.ins().call(func_ref, &[source_val, indices_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD blend: merge two vectors using an indices array
/// a.blend(b, [0, 1, 4, 5]) -> merged vector (0-N from a, N-2N from b)
pub(super) fn compile_vec_blend<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    first: VReg,
    second: VReg,
    indices: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_vec_blend"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let first_val = ctx.vreg_values[&first];
    let second_val = ctx.vreg_values[&second];
    let indices_val = ctx.vreg_values[&indices];
    let call = builder.ins().call(func_ref, &[first_val, second_val, indices_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile SIMD masked select: mask.select(a, b)
/// Returns a where mask is true, b where mask is false
pub(super) fn compile_vec_select<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    mask: VReg,
    if_true: VReg,
    if_false: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_vec_select"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let mask_val = ctx.vreg_values[&mask];
    let if_true_val = ctx.vreg_values[&if_true];
    let if_false_val = ctx.vreg_values[&if_false];
    let call = builder.ins().call(func_ref, &[mask_val, if_true_val, if_false_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile GPU atomic operation: add, sub, min, max, and, or, xor, exchange
/// Returns the old value at the memory location
pub(super) fn compile_gpu_atomic<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    op: crate::mir::GpuAtomicOp,
    ptr: VReg,
    value: VReg,
) {
    use crate::mir::GpuAtomicOp;
    let func_name = match op {
        GpuAtomicOp::Add => "rt_gpu_atomic_add",
        GpuAtomicOp::Sub => "rt_gpu_atomic_sub",
        GpuAtomicOp::Min => "rt_gpu_atomic_min",
        GpuAtomicOp::Max => "rt_gpu_atomic_max",
        GpuAtomicOp::And => "rt_gpu_atomic_and",
        GpuAtomicOp::Or => "rt_gpu_atomic_or",
        GpuAtomicOp::Xor => "rt_gpu_atomic_xor",
        GpuAtomicOp::Xchg => "rt_gpu_atomic_exchange",
    };
    let func_id = ctx.runtime_funcs[func_name];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let ptr_val = ctx.vreg_values[&ptr];
    let value_val = ctx.vreg_values[&value];
    let call = builder.ins().call(func_ref, &[ptr_val, value_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

/// Compile GPU atomic compare-exchange
/// Returns the old value at the memory location
pub(super) fn compile_gpu_atomic_cmpxchg<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    ptr: VReg,
    expected: VReg,
    desired: VReg,
) {
    let func_id = ctx.runtime_funcs["rt_gpu_atomic_cmpxchg"];
    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
    let ptr_val = ctx.vreg_values[&ptr];
    let expected_val = ctx.vreg_values[&expected];
    let desired_val = ctx.vreg_values[&desired];
    let call = builder.ins().call(func_ref, &[ptr_val, expected_val, desired_val]);
    let result = builder.inst_results(call)[0];
    ctx.vreg_values.insert(dest, result);
}

pub(super) fn compile_dict_lit<M: Module>(
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

pub(super) fn compile_index_get<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    collection: VReg,
    index: VReg,
) {
    let index_get_id = ctx.runtime_funcs["rt_index_get"];
    let index_get_ref = ctx.module.declare_func_in_func(index_get_id, builder.func);
    let coll_val = get_vreg_or_default(ctx, builder, &collection);
    let idx_val = get_vreg_or_default(ctx, builder, &index);

    // Wrap index as RuntimeValue (integers need tagging)
    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);
    let wrap_call = builder.ins().call(value_int_ref, &[idx_val]);
    let wrapped_idx = builder.inst_results(wrap_call)[0];

    let call = builder.ins().call(index_get_ref, &[coll_val, wrapped_idx]);
    let runtime_value = builder.inst_results(call)[0];

    // Return the RuntimeValue directly without unwrapping.
    // The result could be any type (string, array, object, etc.) - not just integers.
    // Type-specific unboxing is handled by MirInst::Unbox when needed.
    ctx.vreg_values.insert(dest, runtime_value);
}

pub(super) fn compile_index_set<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    collection: VReg,
    index: VReg,
    value: VReg,
) {
    let index_set_id = ctx.runtime_funcs["rt_index_set"];
    let index_set_ref = ctx.module.declare_func_in_func(index_set_id, builder.func);
    let coll_val = get_vreg_or_default(ctx, builder, &collection);
    let idx_val = get_vreg_or_default(ctx, builder, &index);
    let val = get_vreg_or_default(ctx, builder, &value);

    let value_int_id = ctx.runtime_funcs["rt_value_int"];
    let value_int_ref = ctx.module.declare_func_in_func(value_int_id, builder.func);
    let wrap_idx = builder.ins().call(value_int_ref, &[idx_val]);
    let wrapped_idx = builder.inst_results(wrap_idx)[0];
    let wrap_val = builder.ins().call(value_int_ref, &[val]);
    let wrapped_val = builder.inst_results(wrap_val)[0];

    builder.ins().call(index_set_ref, &[coll_val, wrapped_idx, wrapped_val]);
}

pub(super) fn compile_slice_op<M: Module>(
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

pub(super) fn compile_const_string<M: Module>(
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

pub(super) fn compile_fstring_format<M: Module>(
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
