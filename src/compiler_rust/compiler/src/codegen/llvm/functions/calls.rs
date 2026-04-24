use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

/// Map Simple builtin names to runtime FFI function names.
/// Mirrors the Cranelift backend's name mapping in codegen/instr/calls.rs.
fn map_ffi_name(func_name: &str) -> &str {
    // Strip module prefix to find the base function name
    let base = func_name.rsplit_once("__").map(|(_, tail)| tail).unwrap_or(func_name);
    match base {
        "sys_get_args" => "rt_get_args",
        "sys_exit" => "rt_exit",
        "rt_file_read_text" => "rt_file_read_text_rv",
        "rt_file_delete" => "rt_file_remove",
        "rt_println" => "rt_println_value",
        "rt_print" => "rt_print_value",
        _ => base,
    }
}

/// Returns which Simple-level argument indices are text parameters for a given
/// runtime FFI function. Text arguments are RuntimeValue strings that must be
/// expanded to (ptr, len) pairs when calling the C-ABI FFI function.
/// Mirrors the Cranelift backend's text_arg_indices in codegen/instr/calls.rs.
fn text_arg_indices(func_name: &str) -> Option<&'static [usize]> {
    match func_name {
        // Print/IO (text → ptr, len)
        "rt_print_str" | "rt_println_str" | "rt_eprint_str" | "rt_eprintln_str" => Some(&[0]),

        // Environment variables
        "rt_env_get" | "rt_get_env" | "rt_env_exists" | "rt_env_remove" => Some(&[0]),
        "rt_env_set" | "rt_set_env" => Some(&[0, 1]),

        // File I/O (single path)
        "rt_file_exists"
        | "rt_file_canonicalize"
        | "rt_file_read_text"
        | "rt_file_size"
        | "rt_file_hash_sha256"
        | "rt_file_delete"
        | "rt_file_remove"
        | "rt_file_read_lines"
        | "rt_file_read_bytes" => Some(&[0]),
        // File I/O (two text params: path + content, or src + dest)
        "rt_file_write_text"
        | "rt_file_copy"
        | "rt_file_rename"
        | "rt_file_append_text"
        | "rt_file_write_bytes"
        | "rt_file_move" => Some(&[0, 1]),

        // Directory operations
        "rt_dir_create" | "rt_dir_create_all" | "rt_dir_list" | "rt_dir_remove" | "rt_dir_remove_all"
        | "rt_dir_glob" | "rt_dir_walk" | "rt_set_current_dir" | "rt_dir_exists" => Some(&[0]),
        "rt_file_find" => Some(&[0, 1]),

        // Path operations (single path)
        "rt_path_basename" | "rt_path_dirname" | "rt_path_ext" | "rt_path_absolute" | "rt_path_stem" => Some(&[0]),
        // Path operations (two paths)
        "rt_path_relative" | "rt_path_join" => Some(&[0, 1]),

        // Process execution (cmd is text, args is RuntimeValue array)
        "rt_process_run" | "rt_process_spawn" | "rt_process_execute" => Some(&[0]),
        "rt_process_run_timeout" => Some(&[0]),

        // Contract checking (func_name is text at different positions)
        "simple_contract_check" => Some(&[2]),
        "simple_contract_check_msg" => Some(&[2, 3]),
        "rt_contract_violation_new" => Some(&[1, 2]),

        // Interpreter bridge
        "rt_interp_call" => Some(&[0]),

        // FFI object system (method name at index 1)
        "rt_ffi_call_method" | "rt_ffi_has_method" | "rt_ffi_object_call_method" | "rt_ffi_object_has_method" => {
            Some(&[1])
        }
        "rt_ffi_type_register" => Some(&[0]),

        // BDD test framework
        "rt_bdd_describe_start" | "rt_bdd_it_start" | "rt_bdd_expect_fail" => Some(&[0]),

        // Networking (address is text)
        "native_tcp_bind" | "native_tcp_connect" | "native_udp_bind" => Some(&[0]),
        "native_tcp_connect_timeout" => Some(&[0]),
        "native_tcp_read"
        | "native_tcp_write"
        | "native_tcp_peek"
        | "native_udp_recv_from"
        | "native_udp_recv"
        | "native_udp_send"
        | "native_udp_peek_from"
        | "native_udp_peek" => Some(&[1]),
        "native_udp_connect" => Some(&[1]),
        "native_udp_send_to" => Some(&[1, 2]),

        // Regex (pattern and text)
        "ffi_regex_is_match" | "ffi_regex_find" | "ffi_regex_find_all" | "ffi_regex_captures" | "ffi_regex_split" => {
            Some(&[0, 1])
        }
        "ffi_regex_replace" | "ffi_regex_replace_all" => Some(&[0, 1, 2]),
        "ffi_regex_split_n" => Some(&[0, 1]),

        // Cranelift self-hosting
        "rt_cranelift_new_module" | "rt_cranelift_new_aot_module" => Some(&[0]),
        "rt_cranelift_begin_function" => Some(&[1]),
        "rt_cranelift_get_function_ptr" => Some(&[1]),

        // File stat (path is text, rest are output pointers)
        "rt_file_stat" => Some(&[0]),

        // Native build (takes args RuntimeValue, not text)
        // rt_native_build does NOT have text args — its single arg is a RuntimeValue array
        _ => None,
    }
}

impl LlvmBackend {
    // ============================================================================
    // Call Instructions
    // ============================================================================

    /// Expand text RuntimeValue arguments to (ptr, len) pairs for FFI calls.
    /// Calls rt_string_data and rt_string_len at runtime on each text argument.
    #[cfg(feature = "llvm")]
    fn expand_text_args_llvm(
        &self,
        arg_vals: &[inkwell::values::BasicMetadataValueEnum<'static>],
        text_indices: &[usize],
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<Vec<inkwell::values::BasicMetadataValueEnum<'static>>, CompileError> {
        let i64_type = self.runtime_int_type();

        // Declare rt_string_data and rt_string_len if not already declared
        let string_data_fn = module.get_function("rt_string_data").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_string_data", fn_type, None)
        });
        let string_len_fn = module.get_function("rt_string_len").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_string_len", fn_type, None)
        });

        let mut expanded = Vec::with_capacity(arg_vals.len() + text_indices.len());
        for (i, val) in arg_vals.iter().enumerate() {
            if text_indices.contains(&i) {
                // Expand text RuntimeValue to (ptr, len) pair
                let ptr_call = builder
                    .build_call(string_data_fn, &[*val], "str_data")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_data", &e))?;
                let ptr = ptr_call
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_type.const_int(0, false).into());

                let len_call = builder
                    .build_call(string_len_fn, &[*val], "str_len")
                    .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_len", &e))?;
                let len = len_call
                    .try_as_basic_value()
                    .left()
                    .unwrap_or_else(|| i64_type.const_int(0, false).into());

                expanded.push(ptr.into());
                expanded.push(len.into());
            } else {
                expanded.push(*val);
            }
        }
        Ok(expanded)
    }

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
        let func_name_raw = target.name();
        let ffi_name = map_ffi_name(func_name_raw);
        let i64_type = self.runtime_int_type();

        // Built-in I/O: redirect print/println/eprint/eprintln to runtime functions.
        // Accepts both bare names and spl_ prefixed names (safe symbol exports).
        if matches!(
            func_name_raw,
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
            let (value_fn, ln_value_fn) = match func_name_raw {
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
        if func_name_raw == "substring" && args.len() == 2 {
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
        let bare_rt_redirect: Option<&str> = match func_name_raw {
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
            "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
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
            let returns_bool = matches!(
                rt_fn_name,
                "rt_array_push" | "rt_array_clear" | "rt_array_reverse" | "rt_array_sort" | "rt_index_set"
            );
            let fn_type = if returns_bool {
                self.context.bool_type().fn_type(&param_types, false)
            } else {
                i64_type.fn_type(&param_types, false)
            };
            let rt_func = module
                .get_function(rt_fn_name)
                .unwrap_or_else(|| module.add_function(rt_fn_name, fn_type, None));
            let call_site = builder
                .build_call(rt_func, &arg_vals, "rt_redirect")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt redirect call", &e))?;
            if let Some(d) = dest {
                if let Some(ret_val) = call_site.try_as_basic_value().left() {
                    let ret_val = if returns_bool {
                        self.coerce_value_to_type(ret_val, Some(i64_type.into()), builder)?
                    } else {
                        ret_val
                    };
                    vreg_map.insert(d, ret_val);
                } else {
                    vreg_map.insert(d, i64_type.const_int(0, false).into());
                }
            }
            return Ok(());
        }

        // Resolve through use_map/import_map before declaring (matches Cranelift behavior)
        let resolved_name = self
            .use_map
            .get(func_name_raw)
            .or_else(|| self.import_map.get(func_name_raw))
            .map(|s| s.as_str())
            .unwrap_or(func_name_raw);
        let resolved_dotted = resolved_name.replace("_dot_", ".");
        let raw_dotted = func_name_raw.replace("_dot_", ".");

        // Get or declare the called function (with suffix matching safety net)
        let called_func = module
            .get_function(resolved_name)
            .or_else(|| module.get_function(&resolved_dotted))
            .or_else(|| module.get_function(func_name_raw))
            .or_else(|| module.get_function(&raw_dotted))
            .or_else(|| {
                // Suffix matching: scan module for functions ending with ".{func_name}"
                let suffix_name = if raw_dotted != func_name_raw {
                    raw_dotted.as_str()
                } else {
                    func_name_raw
                };
                let suffix = format!(".{}", suffix_name);
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
                // A candidate is only accepted when its name contains the prefix part.
                // This prevents extern fn names like "c_pcimgr_init" from matching a
                // local method "CNvmeBlockAdapter.init" via the bare suffix "init" when
                // no prefix relationship exists.
                for (i, _) in func_name_raw.match_indices('_').rev() {
                    let method = &func_name_raw[i + 1..];
                    if method.is_empty() {
                        continue;
                    }
                    let suffix = format!(".{}", method);
                    let prefix_part = func_name_raw[..i].to_lowercase();
                    let mut func_opt = module.get_first_function();
                    let mut best: Option<inkwell::values::FunctionValue> = None;
                    while let Some(f) = func_opt {
                        let name = f.get_name().to_string_lossy();
                        if name.ends_with(&suffix) {
                            let has_prefix = prefix_part.is_empty() || name.to_lowercase().contains(&prefix_part);
                            if !has_prefix {
                                func_opt = f.get_next_function();
                                continue;
                            }
                            let dominated = best.as_ref().map_or(true, |b| {
                                let bname = b.get_name().to_string_lossy();
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
                module.add_function(&resolved_dotted, fn_type, None)
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
                    let default_val = self.runtime_int_type().const_int(0, false);
                    vreg_map.insert(d, default_val.into());
                }
                return Ok(());
            }
        };

        {
            let base_ptr = builder
                .build_pointer_cast(closure_ptr, i8_ptr_type, "closure_ptr")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast closure ptr", &e))?;
            let ptr_slot_type = self.context.ptr_type(inkwell::AddressSpace::default());

            let offset_val = self.context.i32_type().const_int(0, false);
            let fn_ptr_slot = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "fn_ptr_slot") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;

            let fn_ptr_slot = builder
                .build_pointer_cast(fn_ptr_slot, ptr_slot_type, "fn_ptr_slot_cast")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn slot ptr", &e))?;

            let func_ptr = builder
                .build_load(i8_ptr_type, fn_ptr_slot, "loaded_func")
                .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;

            if let inkwell::values::BasicValueEnum::PointerValue(fn_ptr) = func_ptr {
                let i64_type = self.runtime_int_type();
                // Prepend closure pointer (coerced to i64) as implicit first argument
                // This matches Cranelift's behavior in closures_structs.rs:67-78
                let closure_as_i64 = builder
                    .build_ptr_to_int(closure_ptr, self.runtime_int_type(), "closure_i64")
                    .map_err(|e| crate::error::factory::llvm_build_failed("ptrtoint", &e))?;
                let mut arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> = vec![closure_as_i64.into()];
                for arg in args {
                    let val = self.get_vreg(arg, vreg_map)?;
                    let casted = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;
                    arg_vals.push(casted.into());
                }

                // Prepend i64 type for the implicit closure pointer parameter.
                // Use actual arg count for function type (param_types from HIR may differ).
                // All args are coerced to i64 matching the tagged-value ABI.
                let mut llvm_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    vec![self.runtime_int_type().into()];
                let user_param_types: Vec<inkwell::types::BasicMetadataTypeEnum> =
                    args.iter().map(|_| i64_type.into()).collect();
                llvm_param_types.extend(user_param_types);

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
                        let default_val = self.runtime_int_type().const_int(0, false);
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
        let i64_type = self.runtime_int_type();
        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let slot_bytes = (i64_type.get_bit_width() / 8) as u64;

        // Declare rt_interp_call if not exists
        let interp_call = module.get_function("rt_interp_call").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
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
        let name_ptr_i64 = builder
            .build_ptr_to_int(name_ptr, i64_type, "func_name_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        let name_len = i64_type.const_int(name_bytes.len() as u64, false);

        let argc = i64_type.const_int(args.len() as u64, false);
        let argv = if args.is_empty() {
            i64_type.const_int(0, false)
        } else {
            let alloc_fn_type = i64_type.fn_type(&[i64_type.into()], false);
            let alloc_fn = module
                .get_function("rt_alloc")
                .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
            let total_bytes = i64_type.const_int(args.len() as u64 * slot_bytes, false);
            let alloc_call = builder
                .build_call(alloc_fn, &[total_bytes.into()], "interp_argv_alloc")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_alloc call", &e))?;
            let argv_raw = alloc_call
                .try_as_basic_value()
                .left()
                .ok_or_else(|| crate::error::factory::llvm_build_failed("rt_alloc result", &"missing return value"))?
                .into_int_value();
            let argv_ptr = builder
                .build_int_to_ptr(argv_raw, i8_ptr_type, "interp_argv_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?;

            for (index, arg) in args.iter().enumerate() {
                let value = self.get_vreg(arg, vreg_map)?;
                let casted = self.coerce_value_to_type(value, Some(i64_type.into()), builder)?;
                let offset = self.context.i32_type().const_int((index as u64) * slot_bytes, false);
                let slot_ptr = unsafe { builder.build_gep(i8_type, argv_ptr, &[offset], "interp_argv_slot") }
                    .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
                let typed_ptr = builder
                    .build_pointer_cast(
                        slot_ptr,
                        self.context.ptr_type(inkwell::AddressSpace::default()),
                        "interp_argv_typed_ptr",
                    )
                    .map_err(|e| crate::error::factory::llvm_cast_failed("cast argv ptr", &e))?;
                builder
                    .build_store(typed_ptr, casted)
                    .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
            }

            argv_raw
        };

        let call_args = [name_ptr_i64.into(), name_len.into(), argc.into(), argv.into()];

        let call_site = builder
            .build_call(interp_call, &call_args, "interp_call")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        if let Some(d) = dest {
            if let Some(ret_val) = call_site.try_as_basic_value().left() {
                vreg_map.insert(d, ret_val);
            } else {
                let default_val = self.runtime_int_type().const_int(0, false);
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
        let i64_type = self.runtime_int_type();

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
            let default_val = self.runtime_int_type().const_int(0, false);
            vreg_map.insert(dest, default_val.into());
        }

        Ok(())
    }
}
