//! Unified instruction compilation for both AOT (cranelift.rs) and JIT (jit.rs) backends.
//!
//! This module provides instruction compilation that works with any Cranelift Module type,
//! eliminating the duplication between cranelift_instr.rs and jit_instr.rs.

use std::collections::HashMap;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;

use crate::hir::{BinOp, TypeId, UnaryOp};
use crate::mir::{BlockId, FStringPart, MirFunction, MirInst, MirLiteral, MirPattern, VReg, BindingStep, PatternBinding, Terminator};

use super::shared::get_func_block_addr;
use super::types_util::{type_id_to_cranelift, type_id_size, type_to_cranelift};

// Include split modules for better organization
include!("instr_methods.rs");
include!("instr_async.rs");
include!("instr_result.rs");
include!("instr_pattern.rs");
include!("instr_collections.rs");

/// Context for instruction compilation, holding all state needed to compile MIR instructions.
pub struct InstrContext<'a, M: Module> {
    pub module: &'a mut M,
    pub func_ids: &'a HashMap<String, cranelift_module::FuncId>,
    pub runtime_funcs: &'a HashMap<&'static str, cranelift_module::FuncId>,
    pub vreg_values: &'a mut HashMap<VReg, cranelift_codegen::ir::Value>,
    pub local_addr_map: &'a mut HashMap<VReg, usize>,
    pub variables: &'a HashMap<usize, cranelift_frontend::Variable>,
    pub func: &'a MirFunction,
    pub entry_block: cranelift_codegen::ir::Block,
    pub blocks: &'a HashMap<BlockId, cranelift_codegen::ir::Block>,
    pub mir_block_id: BlockId,
    pub generator_state_map: &'a Option<HashMap<BlockId, crate::mir::GeneratorState>>,
}

/// Result type for instruction compilation - uses String errors for genericity
pub type InstrResult<T> = Result<T, String>;

/// Compile a single MIR instruction.
pub fn compile_instruction<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    inst: &MirInst,
) -> InstrResult<()> {
    match inst {
        MirInst::ConstInt { dest, value } => {
            let val = builder.ins().iconst(types::I64, *value);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::ConstFloat { dest, value } => {
            let val = builder.ins().f64const(*value);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::ConstBool { dest, value } => {
            let val = builder.ins().iconst(types::I8, if *value { 1 } else { 0 });
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::Copy { dest, src } => {
            let val = ctx.vreg_values[src];
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::BinOp { dest, op, left, right } => {
            let lhs = ctx.vreg_values[left];
            let rhs = ctx.vreg_values[right];
            let val = compile_binop(ctx, builder, *op, lhs, rhs)?;
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::LocalAddr { dest, local_index } => {
            let addr_val = builder.ins().iconst(types::I64, *local_index as i64);
            ctx.vreg_values.insert(*dest, addr_val);
            ctx.local_addr_map.insert(*dest, *local_index);
        }

        MirInst::Load { dest, addr, .. } => {
            if let Some(&local_index) = ctx.local_addr_map.get(addr) {
                if let Some(&var) = ctx.variables.get(&local_index) {
                    let val = builder.use_var(var);
                    ctx.vreg_values.insert(*dest, val);
                }
            } else {
                let val = ctx.vreg_values[addr];
                ctx.vreg_values.insert(*dest, val);
            }
        }

        MirInst::Store { addr, value, .. } => {
            if let Some(&local_index) = ctx.local_addr_map.get(addr) {
                if let Some(&var) = ctx.variables.get(&local_index) {
                    let val = ctx.vreg_values[value];
                    builder.def_var(var, val);
                }
            }
        }

        MirInst::UnaryOp { dest, op, operand } => {
            let val = ctx.vreg_values[operand];
            let result = match op {
                UnaryOp::Neg => builder.ins().ineg(val),
                UnaryOp::Not => builder.ins().icmp_imm(
                    cranelift_codegen::ir::condcodes::IntCC::Equal,
                    val,
                    0,
                ),
                UnaryOp::BitNot => builder.ins().bnot(val),
            };
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::Call { dest, target, args } => {
            let func_name = target.name();

            // Check if this is a built-in I/O function (print, println, etc.)
            if let Some(result) = compile_builtin_io_call(ctx, builder, func_name, args, dest)? {
                if let Some(d) = dest {
                    ctx.vreg_values.insert(*d, result);
                }
            } else if let Some(&callee_id) = ctx.func_ids.get(func_name) {
                // User-defined function
                let callee_ref = ctx.module.declare_func_in_func(callee_id, builder.func);
                let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
                let call = builder.ins().call(callee_ref, &arg_vals);
                if let Some(d) = dest {
                    let results = builder.inst_results(call);
                    if !results.is_empty() {
                        ctx.vreg_values.insert(*d, results[0]);
                    }
                }
            }
        }

        MirInst::GetElementPtr { dest, base, index } => {
            let base_val = ctx.vreg_values[base];
            let index_val = ctx.vreg_values[index];
            let element_size = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(index_val, element_size);
            let addr = builder.ins().iadd(base_val, offset);
            ctx.vreg_values.insert(*dest, addr);
        }

        MirInst::GcAlloc { dest, ty } => {
            let alloc_id = ctx.runtime_funcs["rt_alloc"];
            let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);
            let size = type_id_size(*ty) as i64;
            let size_val = builder.ins().iconst(types::I64, size.max(8));
            let call = builder.ins().call(alloc_ref, &[size_val]);
            let ptr = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, ptr);
        }

        MirInst::Wait { dest, target } => {
            let wait_id = ctx.runtime_funcs["rt_wait"];
            let wait_ref = ctx.module.declare_func_in_func(wait_id, builder.func);
            let target_val = ctx.vreg_values[target];
            let call = builder.ins().call(wait_ref, &[target_val]);
            let result = builder.inst_results(call)[0];
            if let Some(d) = dest {
                ctx.vreg_values.insert(*d, result);
            }
        }

        MirInst::InterpCall { dest, func_name, args } => {
            compile_interp_call(ctx, builder, dest, func_name, args)?;
        }

        MirInst::InterpEval { dest, expr_index } => {
            let interp_eval_id = ctx.runtime_funcs["rt_interp_eval"];
            let interp_eval_ref = ctx.module.declare_func_in_func(interp_eval_id, builder.func);
            let idx = builder.ins().iconst(types::I64, *expr_index as i64);
            let call = builder.ins().call(interp_eval_ref, &[idx]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::ArrayLit { dest, elements } => {
            compile_array_lit(ctx, builder, *dest, elements);
        }

        MirInst::TupleLit { dest, elements } => {
            compile_tuple_lit(ctx, builder, *dest, elements);
        }

        MirInst::DictLit { dest, keys, values } => {
            compile_dict_lit(ctx, builder, *dest, keys, values);
        }

        MirInst::IndexGet { dest, collection, index } => {
            compile_index_get(ctx, builder, *dest, *collection, *index);
        }

        MirInst::IndexSet { collection, index, value } => {
            compile_index_set(ctx, builder, *collection, *index, *value);
        }

        MirInst::SliceOp { dest, collection, start, end, step } => {
            compile_slice_op(ctx, builder, *dest, *collection, *start, *end, *step);
        }

        MirInst::Spread { dest, source } => {
            let source_val = ctx.vreg_values[source];
            ctx.vreg_values.insert(*dest, source_val);
        }

        MirInst::ConstString { dest, value } => {
            compile_const_string(ctx, builder, *dest, value);
        }

        MirInst::ConstSymbol { dest, value } => {
            let hash = value.bytes().enumerate().fold(0i64, |acc, (i, b)| {
                acc.wrapping_add((b as i64).wrapping_mul(31i64.wrapping_pow(i as u32)))
            });
            let symbol_val = builder.ins().iconst(types::I64, hash | (1i64 << 62));
            ctx.vreg_values.insert(*dest, symbol_val);
        }

        MirInst::FStringFormat { dest, parts } => {
            compile_fstring_format(ctx, builder, *dest, parts);
        }

        MirInst::ClosureCreate { dest, func_name, closure_size, capture_offsets, capture_types: _, captures } => {
            compile_closure_create(ctx, builder, *dest, func_name, *closure_size as usize, capture_offsets, captures);
        }

        MirInst::IndirectCall { dest, callee, param_types, return_type, args, effect: _ } => {
            compile_indirect_call(ctx, builder, dest, *callee, param_types, *return_type, args);
        }

        MirInst::StructInit { dest, type_id: _, struct_size, field_offsets, field_types, field_values } => {
            compile_struct_init(ctx, builder, *dest, *struct_size as usize, field_offsets, field_types, field_values);
        }

        MirInst::FieldGet { dest, object, byte_offset, field_type } => {
            let obj_ptr = ctx.vreg_values[object];
            let cranelift_ty = type_id_to_cranelift(*field_type);
            let val = builder.ins().load(cranelift_ty, MemFlags::new(), obj_ptr, *byte_offset as i32);
            ctx.vreg_values.insert(*dest, val);
        }

        MirInst::FieldSet { object, byte_offset, field_type: _, value } => {
            let obj_ptr = ctx.vreg_values[object];
            let val = ctx.vreg_values[value];
            builder.ins().store(MemFlags::new(), val, obj_ptr, *byte_offset as i32);
        }

        MirInst::MethodCallStatic { dest, receiver, func_name, args } => {
            compile_method_call_static(ctx, builder, dest, *receiver, func_name, args)?;
        }

        MirInst::MethodCallVirtual { dest, receiver, vtable_slot, param_types, return_type, args } => {
            compile_method_call_virtual(ctx, builder, dest, *receiver, *vtable_slot as usize, param_types, *return_type, args);
        }

        MirInst::BuiltinMethod { dest, receiver, receiver_type, method, args } => {
            compile_builtin_method(ctx, builder, dest, *receiver, receiver_type, method, args)?;
        }

        MirInst::PatternTest { dest, subject, pattern } => {
            compile_pattern_test(ctx, builder, *dest, *subject, pattern);
        }

        MirInst::PatternBind { dest, subject, binding } => {
            compile_pattern_bind(ctx, builder, *dest, *subject, binding);
        }

        MirInst::EnumDiscriminant { dest, value } => {
            let disc_id = ctx.runtime_funcs["rt_enum_discriminant"];
            let disc_ref = ctx.module.declare_func_in_func(disc_id, builder.func);
            let val = ctx.vreg_values[value];
            let call = builder.ins().call(disc_ref, &[val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::EnumPayload { dest, value } => {
            let payload_id = ctx.runtime_funcs["rt_enum_payload"];
            let payload_ref = ctx.module.declare_func_in_func(payload_id, builder.func);
            let val = ctx.vreg_values[value];
            let call = builder.ins().call(payload_ref, &[val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::EnumUnit { dest, enum_name: _, variant_name } => {
            compile_enum_unit(ctx, builder, *dest, variant_name);
        }

        MirInst::EnumWith { dest, enum_name: _, variant_name, payload } => {
            compile_enum_with(ctx, builder, *dest, variant_name, *payload);
        }

        MirInst::FutureCreate { dest, body_block } => {
            compile_future_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Await { dest, future } => {
            let await_id = ctx.runtime_funcs["rt_future_await"];
            let await_ref = ctx.module.declare_func_in_func(await_id, builder.func);
            let future_val = ctx.vreg_values[future];
            let call = builder.ins().call(await_ref, &[future_val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::ActorSpawn { dest, body_block } => {
            compile_actor_spawn(ctx, builder, *dest, *body_block);
        }

        MirInst::ActorSend { actor, message } => {
            let send_id = ctx.runtime_funcs["rt_actor_send"];
            let send_ref = ctx.module.declare_func_in_func(send_id, builder.func);
            let actor_val = ctx.vreg_values[actor];
            let msg_val = ctx.vreg_values[message];
            builder.ins().call(send_ref, &[actor_val, msg_val]);
        }

        MirInst::ActorRecv { dest } => {
            let recv_id = ctx.runtime_funcs["rt_actor_recv"];
            let recv_ref = ctx.module.declare_func_in_func(recv_id, builder.func);
            let call = builder.ins().call(recv_ref, &[]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::GeneratorCreate { dest, body_block } => {
            compile_generator_create(ctx, builder, *dest, *body_block);
        }

        MirInst::Yield { value } => {
            return compile_yield(ctx, builder, *value);
        }

        MirInst::GeneratorNext { dest, generator } => {
            let next_id = ctx.runtime_funcs["rt_generator_next"];
            let next_ref = ctx.module.declare_func_in_func(next_id, builder.func);
            let gen_val = ctx.vreg_values[generator];
            let call = builder.ins().call(next_ref, &[gen_val]);
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*dest, result);
        }

        MirInst::TryUnwrap { dest, value, error_block, error_dest } => {
            compile_try_unwrap(ctx, builder, *dest, *value, *error_block, *error_dest);
        }

        MirInst::OptionSome { dest, value } => {
            compile_option_some(ctx, builder, *dest, *value);
        }

        MirInst::OptionNone { dest } => {
            compile_option_none(ctx, builder, *dest);
        }

        MirInst::ResultOk { dest, value } => {
            compile_result_ok(ctx, builder, *dest, *value);
        }

        MirInst::ResultErr { dest, value } => {
            compile_result_err(ctx, builder, *dest, *value);
        }
    }
    Ok(())
}

fn compile_binop<M: Module>(
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
        BinOp::Lt => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::SignedLessThan, lhs, rhs),
        BinOp::Gt => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan, lhs, rhs),
        BinOp::LtEq => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::SignedLessThanOrEqual, lhs, rhs),
        BinOp::GtEq => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThanOrEqual, lhs, rhs),
        BinOp::Eq => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, lhs, rhs),
        BinOp::NotEq => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::NotEqual, lhs, rhs),
        BinOp::Is => builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::Equal, lhs, rhs),
        BinOp::In => {
            let contains_id = ctx.runtime_funcs["rt_contains"];
            let contains_ref = ctx.module.declare_func_in_func(contains_id, builder.func);
            let call = builder.ins().call(contains_ref, &[rhs, lhs]);
            builder.inst_results(call)[0]
        }
        BinOp::And => {
            let lhs_bool = builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, lhs, 0);
            let rhs_bool = builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, rhs, 0);
            builder.ins().band(lhs_bool, rhs_bool)
        }
        BinOp::Or => {
            let lhs_bool = builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, lhs, 0);
            let rhs_bool = builder.ins().icmp_imm(cranelift_codegen::ir::condcodes::IntCC::NotEqual, rhs, 0);
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
            let cond = builder.ins().icmp(cranelift_codegen::ir::condcodes::IntCC::SignedGreaterThan, exp_param, zero);
            builder.ins().brif(cond, loop_body, &[], loop_exit, &[result_param]);

            builder.switch_to_block(loop_body);
            let new_result = builder.ins().imul(result_param, lhs);
            let new_exp = builder.ins().isub(exp_param, one);
            builder.ins().jump(loop_header, &[new_result, new_exp]);

            builder.switch_to_block(loop_exit);
            builder.block_params(loop_exit)[0]
        }
        BinOp::FloorDiv => builder.ins().sdiv(lhs, rhs),
    };
    Ok(val)
}

/// Compile built-in I/O function calls (print, println, eprint, eprintln, etc.)
/// Returns Some(result_value) if the function was handled, None if not a built-in I/O function.
fn compile_builtin_io_call<M: Module>(
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
                    let space_data_id = ctx.module
                        .declare_anonymous_data(true, false)
                        .map_err(|e| e.to_string())?;
                    let mut space_desc = cranelift_module::DataDescription::new();
                    space_desc.define(b" ".to_vec().into_boxed_slice());
                    ctx.module.define_data(space_data_id, &space_desc).map_err(|e| e.to_string())?;

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
                let newline_data_id = ctx.module
                    .declare_anonymous_data(true, false)
                    .map_err(|e| e.to_string())?;
                let mut newline_desc = cranelift_module::DataDescription::new();
                newline_desc.define(b"\n".to_vec().into_boxed_slice());
                ctx.module.define_data(newline_data_id, &newline_desc).map_err(|e| e.to_string())?;

                let newline_gv = ctx.module.declare_data_in_func(newline_data_id, builder.func);
                let newline_ptr = builder.ins().global_value(types::I64, newline_gv);
                let newline_len = builder.ins().iconst(types::I64, 1);

                let base_str_fn = if func_name == "println" { "rt_print_str" } else { "rt_eprint_str" };
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

fn compile_interp_call<M: Module>(
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

    let func_name_bytes = func_name.as_bytes();
    let data_id = ctx.module
        .declare_anonymous_data(true, false)
        .map_err(|e| e.to_string())?;
    let mut data_desc = cranelift_module::DataDescription::new();
    data_desc.define(func_name_bytes.to_vec().into_boxed_slice());
    ctx.module.define_data(data_id, &data_desc).map_err(|e| e.to_string())?;

    let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
    let name_ptr = builder.ins().global_value(types::I64, global_val);
    let name_len = builder.ins().iconst(types::I64, func_name_bytes.len() as i64);

    let interp_call_id = ctx.runtime_funcs["rt_interp_call"];
    let interp_call_ref = ctx.module.declare_func_in_func(interp_call_id, builder.func);
    let call = builder.ins().call(interp_call_ref, &[name_ptr, name_len, args_array]);
    let result = builder.inst_results(call)[0];

    if let Some(d) = dest {
        ctx.vreg_values.insert(*d, result);
    }
    Ok(())
}

fn compile_closure_create<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    func_name: &str,
    closure_size: usize,
    capture_offsets: &[u32],
    captures: &[VReg],
) {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);

    let size_val = builder.ins().iconst(types::I64, closure_size as i64);
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let closure_ptr = builder.inst_results(call)[0];

    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let fn_addr = builder.ins().func_addr(types::I64, func_ref);
        builder.ins().store(MemFlags::new(), fn_addr, closure_ptr, 0);
    } else {
        let null = builder.ins().iconst(types::I64, 0);
        builder.ins().store(MemFlags::new(), null, closure_ptr, 0);
    }

    for (i, offset) in capture_offsets.iter().enumerate() {
        let cap_val = ctx.vreg_values[&captures[i]];
        builder.ins().store(MemFlags::new(), cap_val, closure_ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, closure_ptr);
}

fn compile_indirect_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    callee: VReg,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let closure_ptr = ctx.vreg_values[&callee];
    let fn_ptr = builder.ins().load(types::I64, MemFlags::new(), closure_ptr, 0);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![closure_ptr];
    for arg in args {
        call_args.push(ctx.vreg_values[arg]);
    }

    let call = builder.ins().call_indirect(sig_ref, fn_ptr, &call_args);

    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            let null = builder.ins().iconst(types::I64, 0);
            ctx.vreg_values.insert(*d, null);
        }
    }
}

fn compile_struct_init<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: VReg,
    struct_size: usize,
    field_offsets: &[u32],
    field_types: &[TypeId],
    field_values: &[VReg],
) {
    let alloc_id = ctx.runtime_funcs["rt_alloc"];
    let alloc_ref = ctx.module.declare_func_in_func(alloc_id, builder.func);

    let size_val = builder.ins().iconst(types::I64, struct_size as i64);
    let call = builder.ins().call(alloc_ref, &[size_val]);
    let ptr = builder.inst_results(call)[0];

    for (i, (offset, field_type)) in field_offsets.iter().zip(field_types.iter()).enumerate() {
        let field_val = ctx.vreg_values[&field_values[i]];
        let _cranelift_ty = type_id_to_cranelift(*field_type);
        builder.ins().store(MemFlags::new(), field_val, ptr, *offset as i32);
    }

    ctx.vreg_values.insert(dest, ptr);
}

fn compile_method_call_static<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    func_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    if let Some(&func_id) = ctx.func_ids.get(func_name) {
        let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
        let mut call_args = vec![ctx.vreg_values[&receiver]];
        for arg in args {
            call_args.push(ctx.vreg_values[arg]);
        }
        let call = builder.ins().call(func_ref, &call_args);
        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            } else {
                let null = builder.ins().iconst(types::I64, 0);
                ctx.vreg_values.insert(*d, null);
            }
        }
    } else {
        let func_name_bytes = func_name.as_bytes();
        let data_id = ctx.module
            .declare_anonymous_data(true, false)
            .map_err(|e| e.to_string())?;
        let mut data_desc = cranelift_module::DataDescription::new();
        data_desc.define(func_name_bytes.to_vec().into_boxed_slice());
        ctx.module.define_data(data_id, &data_desc).map_err(|e| e.to_string())?;

        let global_val = ctx.module.declare_data_in_func(data_id, builder.func);
        let name_ptr = builder.ins().global_value(types::I64, global_val);
        let name_len = builder.ins().iconst(types::I64, func_name_bytes.len() as i64);

        let not_found_id = ctx.runtime_funcs["rt_function_not_found"];
        let not_found_ref = ctx.module.declare_func_in_func(not_found_id, builder.func);
        let call = builder.ins().call(not_found_ref, &[name_ptr, name_len]);

        if let Some(d) = dest {
            let result = builder.inst_results(call)[0];
            ctx.vreg_values.insert(*d, result);
        }
    }
    Ok(())
}

fn compile_method_call_virtual<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    vtable_slot: usize,
    param_types: &[TypeId],
    return_type: TypeId,
    args: &[VReg],
) {
    let recv_ptr = ctx.vreg_values[&receiver];
    let vtable_ptr = builder.ins().load(types::I64, MemFlags::new(), recv_ptr, 0);
    let slot_offset = (vtable_slot as i32) * 8;
    let method_ptr = builder.ins().load(types::I64, MemFlags::new(), vtable_ptr, slot_offset);

    let call_conv = CallConv::SystemV;
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64));
    for param_ty in param_types {
        sig.params.push(AbiParam::new(type_id_to_cranelift(*param_ty)));
    }
    if return_type != TypeId::VOID {
        sig.returns.push(AbiParam::new(type_id_to_cranelift(return_type)));
    }

    let sig_ref = builder.import_signature(sig);

    let mut call_args = vec![recv_ptr];
    for arg in args {
        call_args.push(ctx.vreg_values[arg]);
    }

    let call = builder.ins().call_indirect(sig_ref, method_ptr, &call_args);

    if let Some(d) = dest {
        let results = builder.inst_results(call);
        if !results.is_empty() {
            ctx.vreg_values.insert(*d, results[0]);
        } else {
            let null = builder.ins().iconst(types::I64, 0);
            ctx.vreg_values.insert(*d, null);
        }
    }
}

/// Compile a complete MIR function body.
/// This is shared between AOT (cranelift.rs) and JIT (jit.rs) backends.
pub fn compile_function_body<M: Module>(
    module: &mut M,
    cranelift_func: &mut cranelift_codegen::ir::Function,
    func: &MirFunction,
    func_ids: &HashMap<String, cranelift_module::FuncId>,
    runtime_funcs: &HashMap<&'static str, cranelift_module::FuncId>,
) -> InstrResult<()> {
    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(cranelift_func, &mut func_ctx);

    // Create variables for parameters and locals
    let mut variables = HashMap::new();
    let mut var_idx = 0u32;

    for (i, param) in func.params.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(param.ty);
        builder.declare_var(var, ty);
        variables.insert(i, var);
        var_idx += 1;
    }

    for (i, local) in func.locals.iter().enumerate() {
        let var = Variable::from_u32(var_idx);
        let ty = type_to_cranelift(local.ty);
        builder.declare_var(var, ty);
        variables.insert(func.params.len() + i, var);
        var_idx += 1;
    }

    // Track values and blocks
    let mut vreg_values: HashMap<VReg, cranelift_codegen::ir::Value> = HashMap::new();

    // Create blocks
    let mut blocks = HashMap::new();
    for mir_block in &func.blocks {
        let cl_block = builder.create_block();
        blocks.insert(mir_block.id, cl_block);
    }

    // Entry block gets parameters
    let entry_block = *blocks.get(&func.entry_block).unwrap();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Initialize parameter variables
    for (i, _param) in func.params.iter().enumerate() {
        let val = builder.block_params(entry_block)[i];
        let var = variables[&i];
        builder.def_var(var, val);
    }

    // If this is an outlined body with captures, load them from ctx (last param).
    if let Some(meta) = func.outlined_bodies.get(&func.entry_block) {
        if !meta.live_ins.is_empty() {
            let ctx_param = if func.generator_states.is_some() {
                let gen_param = builder.block_params(entry_block)[0];
                let get_ctx_id = runtime_funcs["rt_generator_get_ctx"];
                let get_ctx_ref = module.declare_func_in_func(get_ctx_id, builder.func);
                let call = builder.ins().call(get_ctx_ref, &[gen_param]);
                builder.inst_results(call)[0]
            } else {
                builder.block_params(entry_block)[func.params.len().saturating_sub(1)]
            };
            let get_id = runtime_funcs["rt_array_get"];
            let get_ref = module.declare_func_in_func(get_id, builder.func);
            for (idx, reg) in meta.live_ins.iter().enumerate() {
                let idx_val = builder.ins().iconst(types::I64, idx as i64);
                let call = builder.ins().call(get_ref, &[ctx_param, idx_val]);
                let val = builder.inst_results(call)[0];
                vreg_values.insert(*reg, val);
            }
        }
    }

    let generator_states = func.generator_states.clone();
    let generator_state_len = generator_states.as_ref().map(|s| s.len()).unwrap_or(0);
    let generator_state_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.yield_block, s.clone());
        }
        map
    });
    let generator_resume_map = generator_states.as_ref().map(|states| {
        let mut map = HashMap::new();
        for s in states {
            map.insert(s.resume_block, s.clone());
        }
        map
    });
    let mut skip_entry_terminator = false;
    if let Some(states) = &generator_states {
        let generator_param = builder.block_params(entry_block)[0];
        let get_state_id = runtime_funcs["rt_generator_get_state"];
        let get_state_ref = module.declare_func_in_func(get_state_id, builder.func);
        let call = builder.ins().call(get_state_ref, &[generator_param]);
        let state_val = builder.inst_results(call)[0];

        if let Some(entry_target) = func
            .block(func.entry_block)
            .and_then(|b| match b.terminator {
                Terminator::Jump(t) => Some(t),
                _ => None,
            })
        {
            let target_block = *blocks.get(&entry_target).unwrap();
            let mut targets = Vec::new();
            targets.push(target_block);
            for st in states {
                targets.push(*blocks.get(&st.resume_block).unwrap());
            }
            let default_block = func
                .generator_complete
                .and_then(|b| blocks.get(&b).copied())
                .unwrap_or(target_block);

            let mut current_block = entry_block;
            let mut is_first = true;
            for (idx, tgt) in targets.iter().enumerate() {
                if !is_first {
                    builder.switch_to_block(current_block);
                } else {
                    is_first = false;
                }
                let is_last = idx == targets.len() - 1;
                let next_block = if is_last {
                    default_block
                } else {
                    builder.create_block()
                };
                let cmp = builder.ins().icmp_imm(IntCC::Equal, state_val, idx as i64);
                builder.ins().brif(cmp, *tgt, &[], next_block, &[]);
                builder.seal_block(current_block);
                if !is_last {
                    current_block = next_block;
                }
            }
            builder.switch_to_block(default_block);
            skip_entry_terminator = true;
        }
    }

    // Compile each block
    let mut local_addr_map: HashMap<VReg, usize> = HashMap::new();

    for mir_block in &func.blocks {
        if generator_states.is_some() && mir_block.id == func.entry_block {
            continue;
        }
        let cl_block = *blocks.get(&mir_block.id).unwrap();

        if mir_block.id != func.entry_block {
            builder.switch_to_block(cl_block);
        }

        if let Some(resume_map) = generator_resume_map.as_ref() {
            if let Some(state) = resume_map.get(&mir_block.id) {
                let gen_param = builder.block_params(entry_block)[0];
                let load_id = runtime_funcs["rt_generator_load_slot"];
                let load_ref = module.declare_func_in_func(load_id, builder.func);
                for (idx, reg) in state.live_after_yield.iter().enumerate() {
                    let idx_val = builder.ins().iconst(types::I64, idx as i64);
                    let call = builder.ins().call(load_ref, &[gen_param, idx_val]);
                    let val = builder.inst_results(call)[0];
                    vreg_values.insert(*reg, val);
                }
            }
        }

        // Compile instructions
        for inst in &mir_block.instructions {
            let mut instr_ctx = InstrContext {
                module,
                func_ids,
                runtime_funcs,
                vreg_values: &mut vreg_values,
                local_addr_map: &mut local_addr_map,
                variables: &variables,
                func,
                entry_block,
                blocks: &blocks,
                mir_block_id: mir_block.id,
                generator_state_map: &generator_state_map,
            };
            compile_instruction(&mut instr_ctx, &mut builder, inst)?;
        }

        // Compile terminator
        if skip_entry_terminator && mir_block.id == func.entry_block {
            continue;
        }
        match &mir_block.terminator {
            Terminator::Return(val) => {
                if generator_states.is_some() {
                    let gen_param = builder.block_params(entry_block)[0];
                    let set_state_id = runtime_funcs["rt_generator_set_state"];
                    let set_state_ref = module.declare_func_in_func(set_state_id, builder.func);
                    let done_state = builder.ins().iconst(types::I64, generator_state_len as i64);
                    let _ = builder.ins().call(set_state_ref, &[gen_param, done_state]);
                    let mark_id = runtime_funcs["rt_generator_mark_done"];
                    let mark_ref = module.declare_func_in_func(mark_id, builder.func);
                    let _ = builder.ins().call(mark_ref, &[gen_param]);
                }
                if let Some(v) = val {
                    let ret_val = vreg_values[v];
                    builder.ins().return_(&[ret_val]);
                } else if func.return_type == TypeId::VOID {
                    builder.ins().return_(&[]);
                } else {
                    builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
                }
            }

            Terminator::Jump(target) => {
                let target_block = *blocks.get(target).unwrap();
                builder.ins().jump(target_block, &[]);
            }

            Terminator::Branch { cond, then_block, else_block } => {
                let cond_val = vreg_values[cond];
                let then_bl = *blocks.get(then_block).unwrap();
                let else_bl = *blocks.get(else_block).unwrap();
                builder.ins().brif(cond_val, then_bl, &[], else_bl, &[]);
            }

            Terminator::Unreachable => {
                builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(1));
            }
        }
    }

    // Seal all blocks after all predecessors are known
    for mir_block in &func.blocks {
        let cl_block = *blocks.get(&mir_block.id).unwrap();
        builder.seal_block(cl_block);
    }

    builder.finalize();
    Ok(())
}
