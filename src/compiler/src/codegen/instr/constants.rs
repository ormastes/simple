//! Constant value instruction compilation.
//!
//! Handles compilation of constant literals: integers, floats, booleans, strings, and symbols.

use cranelift_codegen::ir::{types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::mir::VReg;

use super::{InstrContext, InstrResult};

/// Compile ConstInt instruction: creates an i64 constant
pub fn compile_const_int<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: i64,
) -> InstrResult<()> {
    let val = builder.ins().iconst(types::I64, value);
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile ConstFloat instruction: creates an f64 constant
pub fn compile_const_float<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: f64,
) -> InstrResult<()> {
    let val = builder.ins().f64const(value);
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile ConstBool instruction: creates an i8 constant (0 or 1)
pub fn compile_const_bool<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: bool,
) -> InstrResult<()> {
    let val = builder.ins().iconst(types::I8, if value { 1 } else { 0 });
    ctx.vreg_values.insert(dest, val);
    Ok(())
}

/// Compile ConstSymbol instruction: creates a symbol hash value
///
/// Symbols are hashed using a simple polynomial rolling hash and tagged with a type bit.
pub fn compile_const_symbol<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    value: &str,
) -> InstrResult<()> {
    // Simple polynomial rolling hash
    let hash = value.bytes().enumerate().fold(0i64, |acc, (i, b)| {
        acc.wrapping_add((b as i64).wrapping_mul(31i64.wrapping_pow(i as u32)))
    });
    // Tag with type bit (bit 62 set for symbol type)
    let symbol_val = builder.ins().iconst(types::I64, hash | (1i64 << 62));
    ctx.vreg_values.insert(dest, symbol_val);
    Ok(())
}
