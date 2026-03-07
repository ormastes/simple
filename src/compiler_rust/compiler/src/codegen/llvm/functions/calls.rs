use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

impl LlvmBackend {
    // ============================================================================
    // Call Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_call(
        &self,
        dest: Option<crate::mir::VReg>,
        target: &crate::mir::CallTarget,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let func_name = target.name();
        let i64_type = self.context.i64_type();

        // Built-in I/O: redirect print/println/eprint/eprintln to runtime functions
        if matches!(func_name, "print" | "println" | "eprint" | "eprintln" | "print_raw" | "eprint_raw" | "dprint") {
            let (value_fn, ln_value_fn) = match func_name {
                "print" | "println" => ("rt_print_value", "rt_println_value"),
                "eprint" | "eprintln" => ("rt_eprint_value", "rt_eprintln_value"),
                "print_raw" => ("rt_print_value", "rt_print_value"),
                "eprint_raw" => ("rt_eprint_value", "rt_eprint_value"),
                "dprint" => ("rt_print_value", "rt_println_value"),
                _ => unreachable!(),
            };

            for (i, arg) in args.iter().enumerate() {
                let val = self.get_vreg(arg, vreg_map)?;
                let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                let is_last = i == args.len() - 1;
                let rt_name = if is_last { ln_value_fn } else { value_fn };

                let rt_func = module.get_function(rt_name).unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function(rt_name, fn_type, None)
                });
                builder
                    .build_call(rt_func, &[casted.into()], "")
                    .map_err(|e| crate::error::factory::llvm_build_failed("print call", &e))?;
            }

            if let Some(d) = dest {
                vreg_map.insert(d, i64_type.const_int(0, false).into());
            }
            return Ok(());
        }

        // Get or declare the called function
        let called_func = module.get_function(func_name).unwrap_or_else(|| {
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(func_name, fn_type, None)
        });

        // Collect argument values
        let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
        for arg in args.iter() {
            let val = self.get_vreg(arg, vreg_map)?;
            let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
            arg_vals.push(casted.into());
        }

        // Check if declared param count matches call arg count
        let declared_params = called_func.get_type().get_param_types().len();
        let call_site = if declared_params != args.len() {
            // Arity mismatch: use indirect call with correct function type
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            let fn_ptr = called_func.as_global_value().as_pointer_value();
            builder
                .build_indirect_call(fn_type, fn_ptr, &arg_vals, "call")
                .map_err(|e| crate::error::factory::llvm_build_failed("indirect call (arity)", &e))?
        } else {
            builder
                .build_call(called_func, &arg_vals, "call")
                .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?
        };

        // Store result if there's a destination
        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            } else {
                let default_val = i64_type.const_int(0, false);
                vreg_map.insert(d, default_val.into());
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_indirect_call(
        &self,
        dest: Option<crate::mir::VReg>,
        callee: crate::mir::VReg,
        param_types: &[crate::hir::TypeId],
        return_type: &crate::hir::TypeId,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        use crate::hir::TypeId;

        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        let callee_val = self.get_vreg(&callee, vreg_map)?;

        // Coerce callee to pointer: i64 values are inttoptr'd (Simple's tagged-value ABI)
        let closure_ptr = match callee_val {
            inkwell::values::BasicValueEnum::PointerValue(p) => p,
            inkwell::values::BasicValueEnum::IntValue(iv) => {
                builder
                    .build_int_to_ptr(iv, i8_ptr_type, "callee_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => {
                // Fallback: insert default dest value and return
                if let Some(d) = dest {
                    let default_val = self.context.i64_type().const_int(0, false);
                    vreg_map.insert(d, default_val.into());
                }
                return Ok(());
            }
        };

        {
            let base_ptr = builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast closure ptr", &e))?;

            let offset_val = self.context.i32_type().const_int(0, false);
            let fn_ptr_slot = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;

            let fn_ptr_slot = builder
                .build_pointer_cast(
                    fn_ptr_slot,
                    i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                    "fn_ptr_slot_cast",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn slot ptr", &e))?;

            let func_ptr = builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;

            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    arg_vals.push(val.into());
                }

                let llvm_param_types: Result<Vec<inkwell::types::BasicMetadataTypeEnum>, CompileError> = param_types
                    .iter()
                    .map(|ty| self.llvm_type(ty).map(|t| t.into()))
                    .collect();
                let llvm_param_types = llvm_param_types?;

                let fn_type = if *return_type == TypeId::VOID {
                    self.context.void_type().fn_type(&llvm_param_types, false)
                } else {
                    let ret_llvm = self.llvm_type(return_type)?;
                    match ret_llvm {
                        BasicTypeEnum::IntType(t) => t.fn_type(&llvm_param_types, false),
                        BasicTypeEnum::FloatType(t) => t.fn_type(&llvm_param_types, false),
                        BasicTypeEnum::PointerType(t) => t.fn_type(&llvm_param_types, false),
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::UNSUPPORTED_FEATURE)
                                .with_help("this return type is not yet supported in indirect calls");
                            return Err(CompileError::semantic_with_context(
                                "Unsupported return type".to_string(),
                                ctx,
                            ));
                        }
                    }
                };

                let call_site = builder
                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                    .map_err(|e| crate::error::factory::llvm_build_failed("indirect call", &e))?;

                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(d, ret_val);
                    } else {
                        let default_val = self.context.i64_type().const_int(0, false);
                        vreg_map.insert(d, default_val.into());
                    }
                }
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_interp_call(
        &self,
        dest: Option<crate::mir::VReg>,
        func_name: &str,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Call interpreter bridge function rt_interp_call
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_interp_call if not exists
        let interp_call = module.get_function("rt_interp_call").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i8_ptr_type.into()],
                false,
            );
            module.add_function("rt_interp_call", fn_type, None)
        });

        // Create string constant for function name
        let name_bytes = func_name.as_bytes();
        let name_const = self.context.const_string(name_bytes, false);
        let name_global = module.add_global(name_const.get_type(), None, "func_name");
        name_global.set_initializer(&name_const);
        name_global.set_constant(true);
        name_global.set_linkage(inkwell::module::Linkage::Private);
        let name_ptr = name_global.as_pointer_value();
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);

        // For now, pass null for args array (simplified)
        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = i8_ptr_type.const_null();

        let call_args = [name_ptr.into(), name_len.into(), argc.into(), argv.into()];

        let call_site = builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            } else {
                let default_val = self.context.i64_type().const_int(0, false);
                vreg_map.insert(d, default_val.into());
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_interp_eval(
        &self,
        dest: crate::mir::VReg,
        expr_index: usize,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Call interpreter to evaluate expression by index
        let i64_type = self.context.i64_type();

        // Declare rt_interp_eval if not exists
        let interp_eval = module.get_function("rt_interp_eval").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_interp_eval", fn_type, None)
        });

        let expr_index_val = i64_type.const_int(expr_index as u64, true);
        let call_site = builder
            .build_call(interp_eval, &[expr_index_val.into()], "eval")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        } else {
            let default_val = self.context.i64_type().const_int(0, false);
            vreg_map.insert(dest, default_val.into());
        }

        Ok(())
    }
}
