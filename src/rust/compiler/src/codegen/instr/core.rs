// Core instruction compilation helpers: binary operations, builtin I/O, and interpreter calls.

use cranelift_codegen::ir::{condcodes::IntCC, types, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;

use crate::hir::BinOp;
use crate::mir::VReg;

use super::helpers::create_string_constant;
use super::{InstrContext, InstrResult};

/// Ensure a value is i64, extending smaller integer types if needed.
/// This is necessary because some values (e.g., from FFI functions returning i32)
/// may not be i64 even though the rest of the codegen assumes i64.
fn ensure_i64(builder: &mut FunctionBuilder, val: cranelift_codegen::ir::Value) -> cranelift_codegen::ir::Value {
    let val_type = builder.func.dfg.value_type(val);
    match val_type {
        types::I8 | types::I16 | types::I32 => builder.ins().sextend(types::I64, val),
        _ => val,
    }
}

pub(crate) fn compile_binop<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    op: BinOp,
    lhs: cranelift_codegen::ir::Value,
    rhs: cranelift_codegen::ir::Value,
) -> InstrResult<cranelift_codegen::ir::Value> {
    let val = match op {
        BinOp::Add => builder.ins().iadd(lhs, rhs),
        BinOp::Sub => builder.ins().isub(lhs, rhs),
        BinOp::Mul => builder.ins().imul(lhs, rhs),
        BinOp::Div => builder.ins().sdiv(lhs, rhs),
        BinOp::Mod => builder.ins().srem(lhs, rhs),
        BinOp::BitAnd => builder.ins().band(lhs, rhs),
        BinOp::BitOr => builder.ins().bor(lhs, rhs),
        BinOp::BitXor => builder.ins().bxor(lhs, rhs),
        BinOp::ShiftLeft => builder.ins().ishl(lhs, rhs),
        BinOp::ShiftRight => builder.ins().sshr(lhs, rhs),
        BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => {
            // Use rt_value_compare for proper comparison of all types (int, float, string/char).
            // rt_value_compare handles raw untagged integers via subnormal-float guards
            // (see equality.rs) so it works for both native codegen integers and heap types.
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let cmp_id = ctx.runtime_funcs["rt_value_compare"];
            let cmp_ref = ctx.module.declare_func_in_func(cmp_id, builder.func);
            let call = builder.ins().call(cmp_ref, &[lhs_i64, rhs_i64]);
            let cmp_result = builder.inst_results(call)[0];
            match op {
                BinOp::Lt => builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::SignedLessThan, cmp_result, 0),
                BinOp::Gt => builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan, cmp_result, 0),
                BinOp::LtEq => builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::SignedLessThanOrEqual, cmp_result, 0),
                BinOp::GtEq => builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual, cmp_result, 0),
                _ => unreachable!(),
            }
        }
        BinOp::Eq => {
            // Use rt_value_eq for deep equality comparison (handles strings, etc.)
            // Ensure both operands are i64 (FFI functions may return smaller types)
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let eq_id = ctx.runtime_funcs["rt_value_eq"];
            let eq_ref = ctx.module.declare_func_in_func(eq_id, builder.func);
            let call = builder.ins().call(eq_ref, &[lhs_i64, rhs_i64]);
            builder.inst_results(call)[0]
        }
        BinOp::NotEq => {
            // Use rt_value_eq and negate the result
            // Ensure both operands are i64 (FFI functions may return smaller types)
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let eq_id = ctx.runtime_funcs["rt_value_eq"];
            let eq_ref = ctx.module.declare_func_in_func(eq_id, builder.func);
            let call = builder.ins().call(eq_ref, &[lhs_i64, rhs_i64]);
            let eq_result = builder.inst_results(call)[0];
            // Negate: eq_result == 0 ? 1 : 0
            builder
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::Equal, eq_result, 0)
        }
        BinOp::Is => builder
            .ins()
            .icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, lhs, rhs),
        BinOp::In | BinOp::NotIn => {
            // Ensure both operands are i64 for runtime function call
            let lhs_i64 = ensure_i64(builder, lhs);
            let rhs_i64 = ensure_i64(builder, rhs);
            let contains_id = ctx.runtime_funcs["rt_contains"];
            let contains_ref = ctx.module.declare_func_in_func(contains_id, builder.func);
            let call = builder.ins().call(contains_ref, &[rhs_i64, lhs_i64]);
            let result = builder.inst_results(call)[0];
            if matches!(op, BinOp::NotIn) {
                // Negate the result for `not in`
                let one = builder.ins().iconst(cranelift_codegen::ir::types::I64, 1);
                builder.ins().bxor(result, one)
            } else {
                result
            }
        }
        BinOp::And | BinOp::AndSuspend => {
            let lhs_bool = builder
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, lhs, 0);
            let rhs_bool = builder
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, rhs, 0);
            builder.ins().band(lhs_bool, rhs_bool)
        }
        BinOp::Or | BinOp::OrSuspend => {
            let lhs_bool = builder
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, lhs, 0);
            let rhs_bool = builder
                .ins()
                .icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, rhs, 0);
            builder.ins().bor(lhs_bool, rhs_bool)
        }
        BinOp::Pow => {
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
            let cond = builder.ins().icmp(
                cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan,
                exp_param,
                zero,
            );
            builder.ins().brif(cond, loop_body, &[], loop_exit, &[result_param]);

            builder.switch_to_block(loop_body);
            let new_result = builder.ins().imul(result_param, lhs);
            let new_exp = builder.ins().isub(exp_param, one);
            builder.ins().jump(loop_header, &[new_result, new_exp]);

            builder.switch_to_block(loop_exit);
            builder.block_params(loop_exit)[0]
        }
        BinOp::FloorDiv => builder.ins().sdiv(lhs, rhs),
        BinOp::MatMul => {
            // Simple Math #1930-#1939: Matrix multiplication requires PyTorch runtime
            return Err("Matrix multiplication (@) requires PyTorch runtime, use interpreter mode".to_string());
        }
        BinOp::PipeForward => {
            // Pipe forward requires function call at runtime
            return Err("Pipe forward (|>) requires interpreter mode for function dispatch".to_string());
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
            let (print_value_fn, print_str_fn) = match func_name {
                "print" => ("rt_print_value", "rt_print_str"),
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

                    // Use the base print_str function (not println)
                    let base_str_fn = match func_name {
                        "println" => "rt_print_str",
                        "eprintln" => "rt_eprint_str",
                        _ => print_str_fn,
                    };
                    let print_str_id = ctx.runtime_funcs[base_str_fn];
                    let print_str_ref = ctx.module.declare_func_in_func(print_str_id, builder.func);
                    builder.ins().call(print_str_ref, &[space_ptr, space_len]);
                }

                // Print the argument value using rt_print_value / rt_println_value
                // For the last arg of println/eprintln, use the ln variant
                let is_last = i == args.len() - 1;
                let fn_to_use = if is_last && (func_name == "println" || func_name == "eprintln") {
                    print_value_fn
                } else {
                    // Use non-newline variant for intermediate args
                    match func_name {
                        "println" => "rt_print_value",
                        "eprintln" => "rt_eprint_value",
                        _ => print_value_fn,
                    }
                };

                let print_id = ctx.runtime_funcs[fn_to_use];
                let print_ref = ctx.module.declare_func_in_func(print_id, builder.func);
                let arg_val = ctx.vreg_values[arg];
                builder.ins().call(print_ref, &[arg_val]);
            }

            // Handle empty print (just prints nothing or newline)
            if args.is_empty() && (func_name == "println" || func_name == "eprintln") {
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

                let base_str_fn = if func_name == "println" {
                    "rt_print_str"
                } else {
                    "rt_eprint_str"
                };
                let print_str_id = ctx.runtime_funcs[base_str_fn];
                let print_str_ref = ctx.module.declare_func_in_func(print_str_id, builder.func);
                builder.ins().call(print_str_ref, &[newline_ptr, newline_len]);
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
    let call = builder.ins().call(array_new_ref, &[capacity]);
    let args_array = builder.inst_results(call)[0];

    let array_push_id = ctx.runtime_funcs["rt_array_push"];
    let array_push_ref = ctx.module.declare_func_in_func(array_push_id, builder.func);

    for arg in args {
        let arg_val = ctx.vreg_values[arg];
        builder.ins().call(array_push_ref, &[args_array, arg_val]);
    }

    let (name_ptr, name_len) = create_string_constant(ctx, builder, func_name)?;

    let interp_call_id = ctx.runtime_funcs["rt_interp_call"];
    let interp_call_ref = ctx.module.declare_func_in_func(interp_call_id, builder.func);
    let call = builder.ins().call(interp_call_ref, &[name_ptr, name_len, args_array]);
    let result = builder.inst_results(call)[0];

    if let Some(d) = dest {
        ctx.vreg_values.insert(*d, result);
    }
    Ok(())
}
