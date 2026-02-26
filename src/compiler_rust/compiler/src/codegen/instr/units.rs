// Unit type operation instruction compilation.

use cranelift_codegen::ir::{condcodes::IntCC, types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::TypeId;
use crate::mir::{UnitOverflowBehavior, VReg};

use super::super::types_util::type_id_to_cranelift;
use super::helpers::create_string_constant;
use super::{InstrContext, InstrResult};

/// Compile a unit bound check instruction.
/// This checks if a value is within the unit type's allowed range.
pub(crate) fn compile_unit_bound_check<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    value: VReg,
    unit_name: &str,
    min: i64,
    max: i64,
    overflow: UnitOverflowBehavior,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&value];

    // Create constants for bounds
    let min_val = builder.ins().iconst(types::I64, min);
    let max_val = builder.ins().iconst(types::I64, max);

    // Check if value is in range: min <= val && val <= max
    let ge_min = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, val, min_val);
    let le_max = builder.ins().icmp(IntCC::SignedLessThanOrEqual, val, max_val);
    let in_range = builder.ins().band(ge_min, le_max);

    match overflow {
        UnitOverflowBehavior::Default | UnitOverflowBehavior::Checked => {
            // Check if we have the runtime unit bound check function
            if let Some(&func_id) = ctx.runtime_funcs.get("simple_unit_bound_check") {
                // Call runtime: simple_unit_bound_check(in_range: bool, value: i64, min: i64, max: i64, name_ptr: *const u8, name_len: i64)
                let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);

                // Create string data for unit name
                let (name_ptr, name_len) = create_string_constant(ctx, builder, unit_name)?;

                // Convert bool to i64 for the call
                let in_range_i64 = builder.ins().uextend(types::I64, in_range);

                builder
                    .ins()
                    .call(func_ref, &[in_range_i64, val, min_val, max_val, name_ptr, name_len]);
            } else {
                // Fallback: generate inline check with trap on failure
                let trap_block = builder.create_block();
                let continue_block = builder.create_block();

                builder.ins().brif(in_range, continue_block, &[], trap_block, &[]);

                builder.switch_to_block(trap_block);
                builder.seal_block(trap_block);
                // Use a generic trap code for unit bound violations
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(10));

                builder.switch_to_block(continue_block);
                builder.seal_block(continue_block);
            }
        }
        UnitOverflowBehavior::Saturate => {
            // Clamp value to [min, max]
            // value = max(min, min(value, max))
            let clamped_high = builder.ins().smin(val, max_val);
            let clamped = builder.ins().smax(clamped_high, min_val);
            ctx.vreg_values.insert(value, clamped);
        }
        UnitOverflowBehavior::Wrap => {
            // Wrap value to [min, max] using modulo
            // wrapped = ((value - min) % range) + min
            // where range = max - min + 1
            let range = builder.ins().isub(max_val, min_val);
            let range_plus_one = builder.ins().iadd_imm(range, 1);
            let offset = builder.ins().isub(val, min_val);
            let wrapped_offset = builder.ins().srem(offset, range_plus_one);
            let wrapped = builder.ins().iadd(wrapped_offset, min_val);
            ctx.vreg_values.insert(value, wrapped);
        }
    }

    Ok(())
}

/// Compile a UnitWiden instruction - widen a unit value to a larger representation.
/// This is a lossless conversion (e.g., u8 → u16, i8 → i32).
pub(crate) fn compile_unit_widen<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    from_bits: u8,
    to_bits: u8,
    signed: bool,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&value];

    // For widening, we just need to extend the value
    let result = if signed {
        // Sign-extend for signed types
        match (from_bits, to_bits) {
            (8, 16) | (8, 32) | (8, 64) | (16, 32) | (16, 64) | (32, 64) => builder.ins().sextend(types::I64, val),
            _ => val, // Same size, just copy
        }
    } else {
        // Zero-extend for unsigned types
        match (from_bits, to_bits) {
            (8, 16) | (8, 32) | (8, 64) | (16, 32) | (16, 64) | (32, 64) => builder.ins().uextend(types::I64, val),
            _ => val, // Same size, just copy
        }
    };

    ctx.vreg_values.insert(dest, result);
    Ok(())
}

/// Compile a UnitNarrow instruction - narrow a unit value to a smaller representation.
/// This may overflow and requires bounds checking.
pub(crate) fn compile_unit_narrow<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    from_bits: u8,
    to_bits: u8,
    signed: bool,
    overflow: UnitOverflowBehavior,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&value];

    // Calculate the bounds for the target type
    let (min, max) = if signed {
        let max_val = (1i64 << (to_bits - 1)) - 1;
        let min_val = -(1i64 << (to_bits - 1));
        (min_val, max_val)
    } else {
        let max_val = (1i64 << to_bits) - 1;
        (0i64, max_val)
    };

    let min_val = builder.ins().iconst(types::I64, min);
    let max_val = builder.ins().iconst(types::I64, max);

    match overflow {
        UnitOverflowBehavior::Default | UnitOverflowBehavior::Checked => {
            // Check if value is in range: min <= val && val <= max
            let ge_min = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, val, min_val);
            let le_max = builder.ins().icmp(IntCC::SignedLessThanOrEqual, val, max_val);
            let in_range = builder.ins().band(ge_min, le_max);

            // Trap if out of range
            let trap_block = builder.create_block();
            let continue_block = builder.create_block();

            builder.ins().brif(in_range, continue_block, &[], trap_block, &[]);

            builder.switch_to_block(trap_block);
            builder.seal_block(trap_block);
            builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(11));

            builder.switch_to_block(continue_block);
            builder.seal_block(continue_block);

            // Value is in range, just truncate/keep as is
            ctx.vreg_values.insert(dest, val);
        }
        UnitOverflowBehavior::Saturate => {
            // Clamp value to [min, max]
            let clamped_high = builder.ins().smin(val, max_val);
            let clamped = builder.ins().smax(clamped_high, min_val);
            ctx.vreg_values.insert(dest, clamped);
        }
        UnitOverflowBehavior::Wrap => {
            // For wrapping, we can use a bitmask for power-of-2 sizes
            let mask = (1i64 << to_bits) - 1;
            let mask_val = builder.ins().iconst(types::I64, mask);
            let wrapped = builder.ins().band(val, mask_val);
            ctx.vreg_values.insert(dest, wrapped);
        }
    }

    Ok(())
}

/// Compile a UnitSaturate instruction - clamp a value to unit bounds.
pub(crate) fn compile_unit_saturate<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: VReg,
    min: i64,
    max: i64,
) -> InstrResult<()> {
    let val = ctx.vreg_values[&value];

    // Create constants for bounds
    let min_val = builder.ins().iconst(types::I64, min);
    let max_val = builder.ins().iconst(types::I64, max);

    // Clamp value to [min, max]
    // value = max(min, min(value, max))
    let clamped_high = builder.ins().smin(val, max_val);
    let clamped = builder.ins().smax(clamped_high, min_val);

    ctx.vreg_values.insert(dest, clamped);
    Ok(())
}
