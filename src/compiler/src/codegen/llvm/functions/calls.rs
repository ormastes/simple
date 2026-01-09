use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

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
    fn compile_call(
        &self,
        dest: Option<crate::mir::VReg>,
        target: &crate::mir::CallTarget,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Get or declare the called function
        let func_name = target.name();
        let called_func = module.get_function(func_name).ok_or_else(|| {
            // Function not found, try to declare it
            // For now, assume all functions return i64 and take i64 params
            let i64_type = self.context.i64_type();
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                args.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            module.add_function(func_name, fn_type, None)
        });

        let called_func = match called_func {
            Ok(f) => f,
            Err(f) => f, // Use the declared function
        };

        // Collect argument values
        let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
        for arg in args {
            let val = self.get_vreg(arg, vreg_map)?;
            arg_vals.push(val.into());
        }

        // Build the call
        let call_site = builder
            .build_call(called_func, &arg_vals, "call")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        // Store result if there's a destination
        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_indirect_call(
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

        if let inkwell::values::BasicValueEnum::PointerValue(closure_ptr) = callee_val {
            let base_ptr = builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| {
                    CompileError::Semantic(format!("Failed to cast closure ptr: {}", e))
                })?;

            let offset_val = self.context.i32_type().const_int(0, false);
            let fn_ptr_slot =
                unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot") }
                    .map_err(|e| CompileError::Semantic(format!("Failed to build gep: {}", e)))?;

            let fn_ptr_slot = builder
                .build_pointer_cast(
                    fn_ptr_slot,
                    i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                    "fn_ptr_slot_cast",
                )
                .map_err(|e| {
                    CompileError::Semantic(format!("Failed to cast fn slot ptr: {}", e))
                })?;

            let func_ptr = builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| CompileError::Semantic(format!("Failed to build load: {}", e)))?;

            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    arg_vals.push(val.into());
                }

                let llvm_param_types: Result<
                    Vec<inkwell::types::BasicMetadataTypeEnum>,
                    CompileError,
                > = param_types
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
                            return Err(CompileError::Semantic(
                                "Unsupported return type".to_string(),
                            ))
                        }
                    }
                };

                let call_site = builder
                    .build_indirect_call(fn_type, fn_ptr, &arg_vals, "indirect_call")
                    .map_err(|e| {
                        CompileError::Semantic(format!("Failed to build indirect call: {}", e))
                    })?;

                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(d, ret_val);
                    }
                }
            }
        } else {
            return Err(CompileError::Semantic(
                "IndirectCall requires closure pointer".to_string(),
            ));
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_interp_call(
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
                &[
                    i8_ptr_type.into(),
                    i64_type.into(),
                    i64_type.into(),
                    i8_ptr_type.into(),
                ],
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
        let name_ptr = name_global.as_pointer_value();
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);

        // For now, pass null for args array (simplified)
        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = i8_ptr_type.const_null();

        let call_args = [name_ptr.into(), name_len.into(), argc.into(), argv.into()];

        let call_site = builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            }
        }

        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_interp_eval(
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
            .map_err(|e| CompileError::Semantic(format!("Failed to build call: {}", e)))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        }

        Ok(())
    }
}
