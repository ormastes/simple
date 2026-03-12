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

        // Built-in I/O: redirect print/println/eprint/eprintln to runtime functions.
        // Accepts both bare names and spl_ prefixed names (safe symbol exports).
        if matches!(
            func_name,
            "print"
                | "println"
                | "eprint"
                | "eprintln"
                | "print_raw"
                | "eprint_raw"
                | "dprint"
                | "spl_print"
                | "spl_println"
                | "spl_eprint"
                | "spl_eprintln"
                | "spl_print_raw"
                | "spl_eprint_raw"
                | "spl_dprint"
        ) {
            let (value_fn, ln_value_fn) = match func_name {
                "print" | "println" | "spl_print" | "spl_println" => ("rt_print_value", "rt_println_value"),
                "eprint" | "eprintln" | "spl_eprint" | "spl_eprintln" => ("rt_eprint_value", "rt_eprintln_value"),
                "print_raw" | "spl_print_raw" => ("rt_print_value", "rt_print_value"),
                "eprint_raw" | "spl_eprint_raw" => ("rt_eprint_value", "rt_eprint_value"),
                "dprint" | "spl_dprint" => ("rt_print_value", "rt_println_value"),
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

        // Special case: substring(text, start) → rt_slice(text, start, rt_len(text), 1)
        // rt_string_substring doesn't exist in the runtime, so we expand to rt_slice + rt_len.
        if func_name == "substring" && args.len() == 2 {
            let text_val = self.get_vreg(&args[0], vreg_map)?;
            let text_casted = self.coerce_value_to_type(text_val, Some(i64_type.into()), builder)?;
            let start_val = self.get_vreg(&args[1], vreg_map)?;
            let start_casted = self.coerce_value_to_type(start_val, Some(i64_type.into()), builder)?;
            // Call rt_len(text) to get the end index
            let len_fn_type = i64_type.fn_type(&[i64_type.into()], false);
            let len_func = module
                .get_function("rt_len")
                .unwrap_or_else(|| module.add_function("rt_len", len_fn_type, None));
            let len_call = builder
                .build_call(len_func, &[text_casted.into()], "text_len")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_len for substring", &e))?;
            let end_val = len_call
                .try_as_basic_value()
                .left()
                .unwrap_or_else(|| i64_type.const_int(0, false).into());
            let step_val = i64_type.const_int(1, false);
            // Call rt_slice(text, start, end, step) — 4 args
            let slice_fn_type = i64_type.fn_type(
                &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            let slice_func = module
                .get_function("rt_slice")
                .unwrap_or_else(|| module.add_function("rt_slice", slice_fn_type, None));
            let slice_args = &[text_casted.into(), start_casted.into(), end_val.into(), step_val.into()];
            let declared_params = slice_func.get_type().get_param_types().len();
            let slice_call = if declared_params != 4 {
                let fn_ptr = slice_func.as_global_value().as_pointer_value();
                builder
                    .build_indirect_call(slice_fn_type, fn_ptr, slice_args, "substr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice for substring", &e))?
            } else {
                builder
                    .build_call(slice_func, slice_args, "substr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_slice for substring", &e))?
            };
            if let Some(d) = dest {
                if let Some(ret_val) = slice_call.try_as_basic_value().left() {
                    vreg_map.insert(d, ret_val);
                } else {
                    vreg_map.insert(d, i64_type.const_int(0, false).into());
                }
            }
            return Ok(());
        }

        // Redirect bare builtin method names to runtime functions.
        // When MIR emits Call { target: "starts_with" } instead of BuiltinMethod,
        // we must map these to rt_* functions. The first arg is the receiver.
        let bare_rt_redirect: Option<&str> = match func_name {
            // String methods (all verified as T symbols in runtime)
            "starts_with" => Some("rt_string_starts_with"),
            "ends_with" => Some("rt_string_ends_with"),
            "contains" => Some("rt_contains"),
            "split" => Some("rt_string_split"),
            "trim" => Some("rt_string_trim"),
            "replace" => Some("rt_string_replace"),
            "to_upper" | "upper" => Some("rt_string_to_upper"),
            "to_lower" | "lower" => Some("rt_string_to_lower"),
            "char_at" => Some("rt_string_char_at"),
            "to_text" | "to_string" => Some("rt_to_string"),
            "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
            "concat" => Some("rt_string_concat"),
            // Array methods (verified as T symbols)
            "push" => Some("rt_array_push"),
            "pop" => Some("rt_array_pop"),
            "sort" => Some("rt_array_sort"),
            "reverse" => Some("rt_array_reverse"),
            "join" => Some("rt_array_join"),
            "clear" => Some("rt_array_clear"),
            "slice" => Some("rt_slice"),
            // Collection methods (verified as T symbols)
            "len" => Some("rt_len"),
            "get" => Some("rt_index_get"),
            "set" => Some("rt_index_set"),
            "keys" => Some("rt_dict_keys"),
            "values" => Some("rt_dict_values"),
            _ => None,
        };

        if let Some(rt_fn_name) = bare_rt_redirect {
            let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
            for arg in args.iter() {
                let val = self.get_vreg(arg, vreg_map)?;
                let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                arg_vals.push(casted.into());
            }
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                arg_vals.iter().map(|_| i64_type.into()).collect();
            let fn_type = i64_type.fn_type(&param_types, false);
            let rt_func = module
                .get_function(rt_fn_name)
                .unwrap_or_else(|| module.add_function(rt_fn_name, fn_type, None));
            let call_site = builder
                .build_call(rt_func, &arg_vals, "rt_redirect")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt redirect call", &e))?;
            if let Some(d) = dest {
                if let Some(ret_val) = call_site.try_as_basic_value().left() {
                    vreg_map.insert(d, ret_val);
                } else {
                    vreg_map.insert(d, i64_type.const_int(0, false).into());
                }
            }
            return Ok(());
        }

        // Map Simple builtin names to runtime FFI names (same as Cranelift backend)
        let ffi_name: &str = match func_name {
            "sys_get_args" => "rt_get_args",
            "sys_exit" => "rt_exit",
            "rt_file_read_text" => "rt_file_read_text_rv",
            "rt_println" => "rt_println_value",
            "rt_print" => "rt_print_value",
            _ => {
                // Strip module prefix for FFI matching
                func_name.rsplit_once("__").map(|(_, tail)| tail).unwrap_or(func_name)
            }
        };

        // Resolve through use_map/import_map before declaring (matches Cranelift behavior)
        let resolved_name = self
            .use_map
            .get(func_name)
            .or_else(|| self.import_map.get(func_name))
            .map(|s| s.as_str())
            .unwrap_or(func_name);

        // Get or declare the called function (with suffix matching safety net)
        let called_func = module
            .get_function(resolved_name)
            .or_else(|| module.get_function(func_name))
            .or_else(|| {
                // Suffix matching: scan module for functions ending with ".{func_name}"
                let suffix = format!(".{}", func_name);
                let mut func_opt = module.get_first_function();
                let mut best: Option<inkwell::values::FunctionValue> = None;
                while let Some(f) = func_opt {
                    let name = f.get_name().to_string_lossy();
                    if name.ends_with(&suffix) {
                        if best
                            .as_ref()
                            .map_or(true, |b| name.len() < b.get_name().to_bytes().len())
                        {
                            best = Some(f);
                        }
                    }
                    func_opt = f.get_next_function();
                }
                best
            })
            .or_else(|| {
                // Split at underscores right-to-left: "tokens_push" → try ".push"
                for (i, _) in func_name.match_indices('_').rev() {
                    let method = &func_name[i + 1..];
                    if method.is_empty() {
                        continue;
                    }
                    let suffix = format!(".{}", method);
                    let prefix_part = func_name[..i].to_lowercase();
                    let mut func_opt = module.get_first_function();
                    let mut best: Option<inkwell::values::FunctionValue> = None;
                    while let Some(f) = func_opt {
                        let name = f.get_name().to_string_lossy();
                        if name.ends_with(&suffix) {
                            let dominated = best.as_ref().map_or(true, |b| {
                                let bname = b.get_name().to_string_lossy();
                                let has_prefix = name.to_lowercase().contains(&prefix_part);
                                let best_has = bname.to_lowercase().contains(&prefix_part);
                                (has_prefix && !best_has) || (has_prefix == best_has && name.len() < bname.len())
                            });
                            if dominated {
                                best = Some(f);
                            }
                        }
                        func_opt = f.get_next_function();
                    }
                    if best.is_some() {
                        return best;
                    }
                }
                None
            })
            .unwrap_or_else(|| {
                let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    args.iter().map(|_| i64_type.into()).collect();
                let fn_type = i64_type.fn_type(&param_types, false);
                module.add_function(resolved_name, fn_type, None)
            });

        // Collect argument values as i64
        let mut raw_arg_vals: Vec<inkwell::values::IntValue> = Vec::new();
        for arg in args.iter() {
            let val = self.get_vreg(arg, vreg_map)?;
            let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
            raw_arg_vals.push(casted.into_int_value());
        }

        // Expand text RuntimeValue arguments to (ptr, len) pairs for FFI calls.
        // This handles the ABI mismatch between Simple (text = RuntimeValue i64)
        // and Rust FFI (text = *const u8 + u64 len).
        let arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> =
            if let Some(text_indices) = crate::codegen::instr::calls::text_arg_indices(ffi_name) {
                let rt_string_data = module.get_function("rt_string_data").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function("rt_string_data", fn_type, None)
                });
                let rt_string_len = module.get_function("rt_string_len").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function("rt_string_len", fn_type, None)
                });
                let mut expanded = Vec::with_capacity(raw_arg_vals.len() + text_indices.len());
                for (i, val) in raw_arg_vals.iter().enumerate() {
                    if text_indices.contains(&i) {
                        // Expand text RuntimeValue to (ptr, len)
                        let ptr_call = builder
                            .build_call(rt_string_data, &[(*val).into()], "str_ptr")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_data", &e))?;
                        let ptr_val = ptr_call
                            .try_as_basic_value()
                            .left()
                            .unwrap_or_else(|| i64_type.const_int(0, false).into());
                        let len_call = builder
                            .build_call(rt_string_len, &[(*val).into()], "str_len")
                            .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_len", &e))?;
                        let len_val = len_call
                            .try_as_basic_value()
                            .left()
                            .unwrap_or_else(|| i64_type.const_int(0, false).into());
                        expanded.push(ptr_val.into());
                        expanded.push(len_val.into());
                    } else {
                        expanded.push((*val).into());
                    }
                }
                expanded
            } else {
                raw_arg_vals.iter().map(|v| (*v).into()).collect()
            };

        // Check if declared param count matches expanded arg count
        let declared_params = called_func.get_type().get_param_types().len();
        let call_site = if declared_params != arg_vals.len() {
            // Arity mismatch: use indirect call with matching function type
            let param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                arg_vals.iter().map(|_| i64_type.into()).collect();
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
            inkwell::values::BasicValueEnum::IntValue(iv) => builder
                .build_int_to_ptr(iv, i8_ptr_type, "callee_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?,
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
                let i64_type = self.context.i64_type();
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = Vec::new();
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                    arg_vals.push(casted.into());
                }

                // Use actual arg count for function type (param_types from HIR may differ).
                // All args are coerced to i64 matching the tagged-value ABI.
                let llvm_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    args.iter().map(|_| i64_type.into()).collect();

                // Default to i64 return (tagged value) — void is rare for indirect calls
                let fn_type = if *return_type == TypeId::VOID {
                    self.context.void_type().fn_type(&llvm_param_types, false)
                } else {
                    i64_type.fn_type(&llvm_param_types, false)
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
