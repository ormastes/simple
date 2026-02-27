// Core instruction compilation helpers: binary operations, builtin I/O, and interpreter calls.

use cranelift_codegen::ir::{condcodes::{FloatCC, IntCC}, types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::BinOp;
use crate::mir::VReg;

use super::helpers::{adapted_call, create_string_constant};
use super::{InstrContext, InstrResult};

/// Ensure a value is i64, extending smaller integer types and bitcasting floats if needed.
/// This is necessary because some values (e.g., from FFI functions returning i32 or
/// float constants) may not be i64 even though runtime functions expect i64.
fn ensure_i64(builder: &mut FunctionBuilder, val: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    let val_type = builder.func.dfg.value_type(val);
    match val_type {
        types::I8 | types::I16 | types::I32 => builder.ins().sextend(types::I64, val),
        types::F64 => builder.ins().bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), val),
        types::F32 => {
            let promoted = builder.ins().fpromote(types::F64, val);
            builder.ins().bitcast(types::I64, cranelift_codegen::ir::MemFlags::new(), promoted)
        }
        _ => val,
    }
}

/// Coerce both operands to matching types for binary operations.
/// If either is float, convert the other to float too.
/// If both are int, ensure both are i64.
fn coerce_binop_operands(
    builder: &mut FunctionBuilder,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
) -> (cranelift_codegen::ir::Value, cranelift_codegen::ir::Value, bool) {
    let lhs_type = builder.func.dfg.value_type(lhs);
    let rhs_type = builder.func.dfg.value_type(rhs);
    let lhs_is_float = lhs_type == types::F32 || lhs_type == types::F64;
    let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;

    if lhs_is_float && rhs_is_float {
        // Both float - promote F32 to F64 if mismatched
        let (l, r) = if lhs_type == types::F32 && rhs_type == types::F64 {
            (builder.ins().fpromote(types::F64, lhs), rhs)
        } else if lhs_type == types::F64 && rhs_type == types::F32 {
            (lhs, builder.ins().fpromote(types::F64, rhs))
        } else {
            (lhs, rhs)
        };
        (l, r, true)
    } else if lhs_is_float && !rhs_is_float {
        // lhs float, rhs int - convert rhs to float
        let target_float = if lhs_type == types::F32 { types::F32 } else { types::F64 };
        let rhs_i64 = ensure_i64(builder, rhs);
        let rhs_f = builder.ins().fcvt_from_sint(target_float, rhs_i64);
        (lhs, rhs_f, true)
    } else if !lhs_is_float && rhs_is_float {
        // lhs int, rhs float - convert lhs to float
        let target_float = if rhs_type == types::F32 { types::F32 } else { types::F64 };
        let lhs_i64 = ensure_i64(builder, lhs);
        let lhs_f = builder.ins().fcvt_from_sint(target_float, lhs_i64);
        (lhs_f, rhs, true)
    } else {
        // Both int - ensure both are i64
        (ensure_i64(builder, lhs), ensure_i64(builder, rhs), false)
    }
}

pub(crate) fn compile_binop<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    op: BinOp,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
) -> InstrResult<cranelift_codegen::ir::Value> {
    // Coerce operands to matching types (handles mixed int/float)
    let (lhs, rhs, is_float) = coerce_binop_operands(builder, lhs, rhs);
    let lhs_type = builder.func.dfg.value_type(lhs);

    let val = match op {
        BinOp::Add => {
            if is_float { builder.ins().fadd(lhs, rhs) }
            else { builder.ins().iadd(lhs, rhs) }
        }
        BinOp::Sub => {
            if is_float { builder.ins().fsub(lhs, rhs) }
            else { builder.ins().isub(lhs, rhs) }
        }
        BinOp::Mul => {
            if is_float { builder.ins().fmul(lhs, rhs) }
            else { builder.ins().imul(lhs, rhs) }
        }
        BinOp::Div => {
            if is_float { builder.ins().fdiv(lhs, rhs) }
            else { builder.ins().sdiv(lhs, rhs) }
        }
        BinOp::Mod => {
            if is_float {
                // Float modulo: a - floor(a/b) * b
                let div = builder.ins().fdiv(lhs, rhs);
                let floored = builder.ins().floor(div);
                let prod = builder.ins().fmul(floored, rhs);
                builder.ins().fsub(lhs, prod)
            } else {
                builder.ins().srem(lhs, rhs)
            }
        }
        BinOp::BitAnd => {
            // Bitwise ops need integer operands
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().band(li, ri)
        }
        BinOp::BitOr => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().bor(li, ri)
        }
        BinOp::BitXor => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().bxor(li, ri)
        }
        BinOp::ShiftLeft => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().ishl(li, ri)
        }
        BinOp::ShiftRight => {
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            builder.ins().sshr(li, ri)
        }
        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
            if is_float {
                // Use native float comparison
                let cc = match op {
                    BinOp::Lt => FloatCC::LessThan,
                    BinOp::Gt => FloatCC::GreaterThan,
                    BinOp::LtEq => FloatCC::LessThanOrEqual,
                    BinOp::GtEq => FloatCC::GreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let cmp_i8 = builder.ins().fcmp(cc, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else {
                // Use rt_value_compare for proper comparison of all types (int, float, string/char).
                let cmp_id = ctx.runtime_funcs["rt_value_compare"];
                let cmp_ref = ctx.module.declare_func_in_func(cmp_id, builder.func);
                let call = adapted_call(builder, cmp_ref, &[lhs, rhs]);
                let cmp_result = builder.inst_results(call)[0];
                let cmp_i8 = match op {
                    BinOp::Lt => builder.ins().icmp_imm(IntCC::SignedLessThan, cmp_result, 0),
                    BinOp::Gt => builder.ins().icmp_imm(IntCC::SignedGreaterThan, cmp_result, 0),
                    BinOp::LtEq => builder.ins().icmp_imm(IntCC::SignedLessThanOrEqual, cmp_result, 0),
                    BinOp::GtEq => builder.ins().icmp_imm(IntCC::SignedGreaterThanOrEqual, cmp_result, 0),
                    _ => unreachable!(),
                };
                ensure_i64(builder, cmp_i8)
            }
        }
        BinOp::Eq => {
            if is_float {
                // Use native float equality
                let cmp_i8 = builder.ins().fcmp(FloatCC::Equal, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else {
                // Use rt_value_eq for deep equality comparison (handles strings, etc.)
                let eq_id = ctx.runtime_funcs["rt_value_eq"];
                let eq_ref = ctx.module.declare_func_in_func(eq_id, builder.func);
                let call = adapted_call(builder, eq_ref, &[lhs, rhs]);
                let result = builder.inst_results(call)[0];
                ensure_i64(builder, result)
            }
        }
        BinOp::NotEq => {
            if is_float {
                // Use native float inequality
                let cmp_i8 = builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs);
                ensure_i64(builder, cmp_i8)
            } else {
                // Use rt_value_eq and negate the result
                let eq_id = ctx.runtime_funcs["rt_value_eq"];
                let eq_ref = ctx.module.declare_func_in_func(eq_id, builder.func);
                let call = adapted_call(builder, eq_ref, &[lhs, rhs]);
                let eq_result = ensure_i64(builder, builder.inst_results(call)[0]);
                let negated = builder.ins().icmp_imm(IntCC::Equal, eq_result, 0);
                ensure_i64(builder, negated)
            }
        }
        BinOp::Is => {
            // Identity comparison - bitcast floats to i64 for bit-level equality
            let li = ensure_i64(builder, lhs);
            let ri = ensure_i64(builder, rhs);
            let result = builder.ins().icmp(IntCC::Equal, li, ri);
            ensure_i64(builder, result)
        }
        BinOp::In | BinOp::NotIn => {
            // Ensure both operands are i64 for runtime function call
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let contains_id = ctx.runtime_funcs["rt_contains"];
            let contains_ref = ctx.module.declare_func_in_func(contains_id, builder.func);
            let call = adapted_call(builder, contains_ref, &[rhs_i64, lhs_i64]);
            let result = ensure_i64(builder, builder.inst_results(call)[0]);
            if matches!(op, BinOp::NotIn) {
                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().bxor(result, one)
            } else {
                result
            }
        }
        BinOp::And | BinOp::AndSuspend => {
            let lhs_bool = if is_float {
                let zero_f = if lhs_type == types::F32 { builder.ins().f32const(0.0) } else { builder.ins().f64const(0.0) };
                builder.ins().fcmp(FloatCC::NotEqual, lhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0)
            };
            let rhs_type = builder.func.dfg.value_type(rhs);
            let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;
            let rhs_bool = if rhs_is_float {
                let zero_f = if rhs_type == types::F32 { builder.ins().f32const(0.0) } else { builder.ins().f64const(0.0) };
                builder.ins().fcmp(FloatCC::NotEqual, rhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, rhs, 0)
            };
            let result = builder.ins().band(lhs_bool, rhs_bool);
            ensure_i64(builder, result)
        }
        BinOp::Or | BinOp::OrSuspend => {
            let lhs_bool = if is_float {
                let zero_f = if lhs_type == types::F32 { builder.ins().f32const(0.0) } else { builder.ins().f64const(0.0) };
                builder.ins().fcmp(FloatCC::NotEqual, lhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, lhs, 0)
            };
            let rhs_type = builder.func.dfg.value_type(rhs);
            let rhs_is_float = rhs_type == types::F32 || rhs_type == types::F64;
            let rhs_bool = if rhs_is_float {
                let zero_f = if rhs_type == types::F32 { builder.ins().f32const(0.0) } else { builder.ins().f64const(0.0) };
                builder.ins().fcmp(FloatCC::NotEqual, rhs, zero_f)
            } else {
                builder.ins().icmp_imm(IntCC::NotEqual, rhs, 0)
            };
            let result = builder.ins().bor(lhs_bool, rhs_bool);
            ensure_i64(builder, result)
        }
        BinOp::Pow => {
            if is_float {
                // Float power: fall back to integer exponent loop with fmul
                let rhs_type = builder.func.dfg.value_type(rhs);
                let rhs_i64 = if rhs_type.is_float() {
                    builder.ins().fcvt_to_sint(types::I64, rhs)
                } else {
                    ensure_i64(builder, rhs)
                };
                let loop_header = builder.create_block();
                let loop_body = builder.create_block();
                let loop_exit = builder.create_block();

                builder.append_block_param(loop_header, lhs_type); // result (float)
                builder.append_block_param(loop_header, types::I64); // exponent (int)
                builder.append_block_param(loop_exit, lhs_type); // final result (float)

                let one_f = if lhs_type == types::F32 { builder.ins().f32const(1.0) } else { builder.ins().f64const(1.0) };
                builder.ins().jump(loop_header, &[one_f, rhs_i64]);

                builder.switch_to_block(loop_header);
                let result_param = builder.block_params(loop_header)[0];
                let exp_param = builder.block_params(loop_header)[1];
                let zero = builder.ins().iconst(types::I64, 0);
                let cond = builder.ins().icmp(IntCC::SignedGreaterThan, exp_param, zero);
                builder.ins().brif(cond, loop_body, &[], loop_exit, &[result_param]);

                builder.switch_to_block(loop_body);
                let new_result = builder.ins().fmul(result_param, lhs);
                let one_i = builder.ins().iconst(types::I64, 1);
                let new_exp = builder.ins().isub(exp_param, one_i);
                builder.ins().jump(loop_header, &[new_result, new_exp]);

                builder.switch_to_block(loop_exit);
                builder.block_params(loop_exit)[0]
            } else {
                let loop_header = builder.create_block();
                let loop_body = builder.create_block();
                let loop_exit = builder.create_block();

                builder.append_block_param(loop_header, types::I64);
                builder.append_block_param(loop_header, types::I64);
                builder.append_block_param(loop_exit, types::I64);

                let one = builder.ins().iconst(types::I64, 1);
                builder.ins().jump(loop_header, &[one, rhs]);

                builder.switch_to_block(loop_header);
                let result_param = builder.block_params(loop_header)[0];
                let exp_param = builder.block_params(loop_header)[1];
                let zero = builder.ins().iconst(types::I64, 0);
                let cond = builder.ins().icmp(IntCC::SignedGreaterThan, exp_param, zero);
                builder.ins().brif(cond, loop_body, &[], loop_exit, &[result_param]);

                builder.switch_to_block(loop_body);
                let new_result = builder.ins().imul(result_param, lhs);
                let new_exp = builder.ins().isub(exp_param, one);
                builder.ins().jump(loop_header, &[new_result, new_exp]);

                builder.switch_to_block(loop_exit);
                builder.block_params(loop_exit)[0]
            }
        }
        BinOp::MatMul => {
            // Matrix multiplication (@) - Simple Math #1930-#1939
            // Codegen requires runtime library support for dynamic array operations
            // Use interpreter mode (default) for full matrix multiplication support
            return Err(
                "Matrix multiplication (@) requires runtime library, use interpreter mode (already implemented)"
                    .to_string(),
            );
        }
        BinOp::PipeForward => {
            // Pipe forward requires function call at runtime
            return Err("Pipe forward (|>) requires interpreter mode for function dispatch".to_string());
        }
        BinOp::Parallel => {
            // Parallel execution requires async runtime
            return Err("Parallel operator (//) requires interpreter mode for concurrent execution".to_string());
        }
    };
    Ok(val)
}

/// Compile built-in I/O function calls (print, println, eprint, eprintln, etc.)
/// Returns Some(result_value) if the function was handled, None if not a built-in I/O function.
pub(crate) fn compile_builtin_io_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    func_name: &str,
    args: &[VReg],
    _dest: &Option<VReg>,
) -> InstrResult<Option<cranelift_codegen::ir::Value>> {
    match func_name {
        "print" | "println" | "eprint" | "eprintln" => {
            // Determine which runtime function to use
            // Note: In Simple, 'print' adds a newline (Python 3 convention)
            let (print_value_fn, print_str_fn) = match func_name {
                "print" => ("rt_println_value", "rt_println_str"),
                "println" => ("rt_println_value", "rt_println_str"),
                "eprint" => ("rt_eprint_value", "rt_eprint_str"),
                "eprintln" => ("rt_eprintln_value", "rt_eprintln_str"),
                _ => unreachable!(),
            };

            // For each argument, call the appropriate print function
            for (i, arg) in args.iter().enumerate() {
                // Add space between arguments (except first)
                if i > 0 {
                    // Print a space separator
                    let space_data_id = ctx
                        .module
                        .declare_anonymous_data(true, false)
                        .map_err(|e| e.to_string())?;
                    let mut space_desc = cranelift_module::DataDescription::new();
                    space_desc.define(b" ".to_vec().into_boxed_slice());
                    ctx.module
                        .define_data(space_data_id, &space_desc)
                        .map_err(|e| e.to_string())?;

                    let space_gv = ctx.module.declare_data_in_func(space_data_id, builder.func);
                    let space_ptr = builder.ins().global_value(types::I64, space_gv);
                    let space_len = builder.ins().iconst(types::I64, 1);

                    // Use the base print_str function (not println) for space separator
                    let base_str_fn = match func_name {
                        "print" => "rt_print_str",
                        "println" => "rt_print_str",
                        "eprintln" => "rt_eprint_str",
                        _ => print_str_fn,
                    };
                    let print_str_id = ctx.runtime_funcs[base_str_fn];
                    let print_str_ref = ctx.module.declare_func_in_func(print_str_id, builder.func);
                    adapted_call(builder, print_str_ref, &[space_ptr, space_len]);
                }

                // Print the argument value using rt_print_value / rt_println_value
                // For the last arg of print/println/eprintln, use the ln variant
                let is_last = i == args.len() - 1;
                let fn_to_use =
                    if is_last && (func_name == "print" || func_name == "println" || func_name == "eprintln") {
                        print_value_fn
                    } else {
                        // Use non-newline variant for intermediate args
                        match func_name {
                            "print" => "rt_print_value",
                            "println" => "rt_print_value",
                            "eprintln" => "rt_eprint_value",
                            _ => print_value_fn,
                        }
                    };

                let print_id = ctx.runtime_funcs[fn_to_use];
                let print_ref = ctx.module.declare_func_in_func(print_id, builder.func);
                let arg_val = match ctx.vreg_values.get(arg) {
                    Some(&v) => v,
                    None => return Err(format!("print: arg vreg {:?} not found", arg)),
                };
                adapted_call(builder, print_ref, &[arg_val]);
            }

            // Handle empty print (just prints nothing or newline)
            if args.is_empty() && (func_name == "print" || func_name == "println" || func_name == "eprintln") {
                // Print just a newline
                let newline_data_id = ctx
                    .module
                    .declare_anonymous_data(true, false)
                    .map_err(|e| e.to_string())?;
                let mut newline_desc = cranelift_module::DataDescription::new();
                newline_desc.define(b"\n".to_vec().into_boxed_slice());
                ctx.module
                    .define_data(newline_data_id, &newline_desc)
                    .map_err(|e| e.to_string())?;

                let newline_gv = ctx.module.declare_data_in_func(newline_data_id, builder.func);
                let newline_ptr = builder.ins().global_value(types::I64, newline_gv);
                let newline_len = builder.ins().iconst(types::I64, 1);

                let base_str_fn = if func_name == "print" || func_name == "println" {
                    "rt_print_str"
                } else {
                    "rt_eprint_str"
                };
                let print_str_id = ctx.runtime_funcs[base_str_fn];
                let print_str_ref = ctx.module.declare_func_in_func(print_str_id, builder.func);
                adapted_call(builder, print_str_ref, &[newline_ptr, newline_len]);
            }

            // Return nil (0) for void functions
            let nil = builder.ins().iconst(types::I64, 0);
            Ok(Some(nil))
        }
        // Not a built-in I/O function
        _ => Ok(None),
    }
}

pub(crate) fn compile_interp_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    func_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    let array_new_id = ctx.runtime_funcs["rt_array_new"];
    let array_new_ref = ctx.module.declare_func_in_func(array_new_id, builder.func);
    let capacity = builder.ins().iconst(types::I64, args.len() as i64);
    let call = adapted_call(builder, array_new_ref, &[capacity]);
    let args_array = builder.inst_results(call)[0];

    let array_push_id = ctx.runtime_funcs["rt_array_push"];
    let array_push_ref = ctx.module.declare_func_in_func(array_push_id, builder.func);

    for arg in args {
        let arg_val = match ctx.vreg_values.get(arg) {
            Some(&v) => v,
            None => return Err(format!("interp_call: arg vreg {:?} not found", arg)),
        };
        adapted_call(builder, array_push_ref, &[args_array, arg_val]);
    }

    let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

    let interp_call_id = ctx.runtime_funcs["rt_interp_call"];
    let interp_call_ref = ctx.module.declare_func_in_func(interp_call_id, builder.func);
    let call = adapted_call(builder, interp_call_ref, &[name_ptr, name_len, args_array]);
    let result = builder.inst_results(call)[0];

    if let Some(d) = dest {
        ctx.vreg_values.insert(*d, result);
    }
    Ok(())
}
