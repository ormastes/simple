//! Extern class FFI method call compilation.
//!
//! This module handles codegen for `extern class` method calls, generating
//! calls to the runtime FFI object system (rt_ffi_object_call_method).

use cranelift_codegen::ir::{types, AbiParam, InstBuilder, MemFlags, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_module::Module;

use cranelift_frontend::FunctionBuilder;

use crate::mir::VReg;

use super::{InstrContext, InstrResult};

/// Compile an extern class method call.
///
/// For static methods: calls `rt_ffi_object_call_method` with a null receiver
/// For instance methods: calls `rt_ffi_object_call_method` with the receiver object
///
/// The runtime function signature is:
/// `rt_ffi_object_call_method(obj: i64, method_name_ptr: i64, method_name_len: i64, argc: i64, argv: i64) -> i64`
pub fn compile_extern_method_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: Option<VReg>,
    class_name: &str,
    method_name: &str,
    is_static: bool,
    args: &[VReg],
) -> InstrResult<()> {
    // For static methods, we need to get the type and call a static factory
    // For instance methods, we call the method on the receiver object

    if is_static {
        // Static method call: ClassName::method_name(args...)
        // We use a convention where static methods are called via rt_ffi_call_static
        // The method name is "ClassName::method_name"
        let full_method_name = format!("{}::{}", class_name, method_name);
        compile_ffi_static_call(ctx, builder, dest, &full_method_name, args)?;
    } else {
        // Instance method call: receiver.method_name(args...)
        let recv = receiver.expect("Instance method call requires receiver");
        compile_ffi_instance_call(ctx, builder, dest, recv, method_name, args)?;
    }

    Ok(())
}

/// Compile a static FFI method call (factory methods like ClassName::open).
///
/// These are dispatched through the type registry to find the appropriate
/// constructor or static method.
fn compile_ffi_static_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    full_method_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    // Get the runtime function for calling static methods
    // For now, we'll use a naming convention: the function is named rt_<ClassName>_<method>
    // Or we can use a generic dispatcher: rt_ffi_call_static(class_name_ptr, class_name_len, method_name_ptr, method_name_len, argc, argv)

    // For simplicity, let's use the generic dispatcher approach
    // We need to:
    // 1. Create a data section for the method name string
    // 2. Get the pointer to the method name
    // 3. Build the argument array
    // 4. Call rt_ffi_object_call_method with null receiver for static methods

    // Build argument array on stack
    let argc = args.len() as i64;
    let argc_val = builder.ins().iconst(types::I64, argc);

    // Allocate space for arguments array (each arg is i64)
    let argv_ptr = if argc > 0 {
        // Stack allocate: 8 bytes per argument
        let stack_slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (argc as u32) * 8,
            0,
        ));
        let base_addr = builder.ins().stack_addr(types::I64, stack_slot, 0);

        // Store each argument
        for (i, arg) in args.iter().enumerate() {
            let arg_val = ctx.vreg_values[arg];
            let offset = (i * 8) as i32;
            builder
                .ins()
                .store(MemFlags::new(), arg_val, base_addr, offset);
        }
        base_addr
    } else {
        builder.ins().iconst(types::I64, 0) // null pointer for empty args
    };

    // Create method name string constant
    let method_name_ptr = builder.ins().iconst(types::I64, full_method_name.as_ptr() as i64);
    let method_name_len = builder.ins().iconst(types::I64, full_method_name.len() as i64);

    // For static methods, receiver is 0 (null)
    let null_receiver = builder.ins().iconst(types::I64, 0);

    // Call rt_ffi_object_call_method(null, method_name_ptr, method_name_len, argc, argv)
    if let Some(&runtime_id) = ctx.runtime_funcs.get("rt_ffi_object_call_method") {
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
        let call = builder.ins().call(
            runtime_ref,
            &[null_receiver, method_name_ptr, method_name_len, argc_val, argv_ptr],
        );

        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    } else {
        // Fallback: try to find a direct function with the naming convention
        // rt_<class>_<method>
        let direct_func_name = format!(
            "rt_{}_{}",
            full_method_name.split("::").next().unwrap_or("").to_lowercase(),
            full_method_name.split("::").last().unwrap_or("")
        );

        if let Some(&func_id) = ctx.runtime_funcs.get(direct_func_name.as_str()) {
            let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
            let arg_vals: Vec<_> = args.iter().map(|a| ctx.vreg_values[a]).collect();
            let call = builder.ins().call(func_ref, &arg_vals);

            if let Some(d) = dest {
                let results = builder.inst_results(call);
                if !results.is_empty() {
                    ctx.vreg_values.insert(*d, results[0]);
                }
            }
        }
    }

    Ok(())
}

/// Compile an instance FFI method call (methods on FFI objects).
///
/// The receiver is an FFI object (RuntimeValue with FfiObject heap type),
/// and we call rt_ffi_object_call_method to dispatch to the appropriate method.
fn compile_ffi_instance_call<M: Module>(
    ctx: &mut InstrContext<'_, M>,
    builder: &mut FunctionBuilder,
    dest: &Option<VReg>,
    receiver: VReg,
    method_name: &str,
    args: &[VReg],
) -> InstrResult<()> {
    // Get receiver value
    let recv_val = ctx.vreg_values[&receiver];

    // Build argument array on stack
    let argc = args.len() as i64;
    let argc_val = builder.ins().iconst(types::I64, argc);

    // Allocate space for arguments array
    let argv_ptr = if argc > 0 {
        let stack_slot = builder.create_sized_stack_slot(cranelift_codegen::ir::StackSlotData::new(
            cranelift_codegen::ir::StackSlotKind::ExplicitSlot,
            (argc as u32) * 8,
            0,
        ));
        let base_addr = builder.ins().stack_addr(types::I64, stack_slot, 0);

        for (i, arg) in args.iter().enumerate() {
            let arg_val = ctx.vreg_values[arg];
            let offset = (i * 8) as i32;
            builder
                .ins()
                .store(MemFlags::new(), arg_val, base_addr, offset);
        }
        base_addr
    } else {
        builder.ins().iconst(types::I64, 0)
    };

    // Create method name string constant
    // Note: This creates a dangling pointer to stack data - in production,
    // we'd want to use a proper string table or data section
    let method_name_ptr = builder.ins().iconst(types::I64, method_name.as_ptr() as i64);
    let method_name_len = builder.ins().iconst(types::I64, method_name.len() as i64);

    // Call rt_ffi_object_call_method(receiver, method_name_ptr, method_name_len, argc, argv)
    if let Some(&runtime_id) = ctx.runtime_funcs.get("rt_ffi_object_call_method") {
        let runtime_ref = ctx.module.declare_func_in_func(runtime_id, builder.func);
        let call = builder.ins().call(
            runtime_ref,
            &[recv_val, method_name_ptr, method_name_len, argc_val, argv_ptr],
        );

        if let Some(d) = dest {
            let results = builder.inst_results(call);
            if !results.is_empty() {
                ctx.vreg_values.insert(*d, results[0]);
            }
        }
    }

    Ok(())
}
