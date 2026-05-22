use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;
#[cfg(feature = "llvm")]
use inkwell::values::BasicValue;
#[cfg(feature = "llvm")]
use inkwell::IntPredicate;

/// Map Simple builtin names to runtime SFFI function names.
/// Mirrors the Cranelift backend's name mapping in codegen/instr/calls.rs.
fn map_sffi_name(func_name: &str) -> &str {
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

fn qualified_runtime_arity(method: &str, rt_name: &str) -> Option<usize> {
    match rt_name {
        "rt_len" | "rt_to_string" | "rt_string_to_int" | "rt_string_to_float" | "rt_string_to_upper"
        | "rt_string_to_lower" | "rt_string_trim" | "rt_array_pop" | "rt_array_sort" | "rt_array_reverse"
        | "rt_array_clear" | "rt_dict_keys" | "rt_dict_values" | "rt_is_none" | "rt_is_some" | "rt_enum_payload" => {
            Some(1)
        }
        "rt_string_starts_with"
        | "rt_string_ends_with"
        | "rt_contains"
        | "rt_string_split"
        | "rt_string_concat"
        | "rt_string_rfind"
        | "rt_array_push"
        | "rt_index_get"
        | "rt_index_set"
        | "rt_enum_check_discriminant"
        | "lib__common__string_core__str_repeat" => Some(2),
        _ if matches!(method, "slice" | "substring") => Some(2),
        _ => None,
    }
}

/// Returns which Simple-level argument indices are text parameters for a given
/// runtime SFFI function. Text arguments are RuntimeValue strings that must be
/// expanded to (ptr, len) pairs when calling the C-ABI SFFI function.
/// Mirrors the Cranelift backend's text_arg_indices in codegen/instr/calls.rs.
fn text_arg_indices(func_name: &str) -> Option<&'static [usize]> {
    match func_name {
        // Print/IO (text → ptr, len)
        "rt_print_str" | "rt_println_str" | "rt_eprint_str" | "rt_eprintln_str" => Some(&[0]),

        // Environment variables
        "rt_env_get" | "rt_env_get_i64" | "rt_get_env" | "rt_env_exists" | "rt_env_remove" => Some(&[0]),
        "rt_env_set" | "rt_set_env" => Some(&[0, 1]),

        // File I/O (single path)
        "rt_file_exists"
        | "rt_file_canonicalize"
        | "rt_file_read_text"
        | "rt_file_size"
        | "rt_file_hash_sha256"
        | "rt_file_fsync"
        | "rt_file_fsync_cached"
        | "rt_file_delete"
        | "rt_file_remove"
        | "rt_file_read_lines"
        | "rt_file_read_bytes"
        | "rt_file_mmap_read_text"
        | "rt_file_mmap_len"
        | "rt_file_mmap_read_bytes" => Some(&[0]),
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

        // Async I/O driver text arguments
        "rt_driver_submit_open" => Some(&[1]),
        "rt_driver_submit_connect" | "rt_driver_submit_send" | "rt_driver_submit_write" => Some(&[2]),

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

        // SFFI object system (method name at index 1)
        "rt_sffi_call_method" | "rt_sffi_has_method" | "rt_sffi_object_call_method" | "rt_sffi_object_has_method" => {
            Some(&[1])
        }
        "rt_sffi_type_register" => Some(&[0]),

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
        "sffi_regex_is_match"
        | "sffi_regex_find"
        | "sffi_regex_find_all"
        | "sffi_regex_captures"
        | "sffi_regex_split" => Some(&[0, 1]),
        "sffi_regex_replace" | "sffi_regex_replace_all" => Some(&[0, 1, 2]),
        "sffi_regex_split_n" => Some(&[0, 1]),

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

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_inline_len(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        trusted_array: bool,
    ) -> Result<bool, CompileError> {
        if args.len() != 1 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let current_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM builder has no insert block for rt_len".to_string()))?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let invalid = i64_type.const_int((-1i64) as u64, true);

        let value = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        if trusted_array {
            let ptr_bits = builder
                .build_and(value, i64_type.const_int(!7u64, false), "array_len_ptr_bits")
                .map_err(|e| crate::error::factory::llvm_build_failed("array len ptr bits", &e))?;
            let object_ptr = builder
                .build_int_to_ptr(ptr_bits, ptr_type, "array_len_object_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("array len int_to_ptr", &e))?;
            let len_ptr = unsafe {
                builder
                    .build_gep(i8_type, object_ptr, &[i64_type.const_int(8, false)], "array_len_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("array len gep", &e))?
            };
            let len = builder
                .build_load(i64_type, len_ptr, "array_len_value")
                .map_err(|e| crate::error::factory::llvm_build_failed("array len load", &e))?;
            vreg_map.insert(dest, len);
            return Ok(true);
        }
        let tag = builder
            .build_and(value, i64_type.const_int(7, false), "len_tag")
            .map_err(|e| crate::error::factory::llvm_build_failed("len tag", &e))?;
        let is_heap = builder
            .build_int_compare(IntPredicate::EQ, tag, i64_type.const_int(1, false), "len_is_heap")
            .map_err(|e| crate::error::factory::llvm_build_failed("len heap check", &e))?;

        let type_block = self.context_ref().append_basic_block(function, "len_type");
        let len_block = self.context_ref().append_basic_block(function, "len_load");
        let done_block = self.context_ref().append_basic_block(function, "len_done");
        builder
            .build_conditional_branch(is_heap, type_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("len heap branch", &e))?;

        builder.position_at_end(type_block);
        let ptr_bits = builder
            .build_and(value, i64_type.const_int(!7u64, false), "len_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("len ptr bits", &e))?;
        let object_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "len_object_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("len int_to_ptr", &e))?;
        let object_type = builder
            .build_load(i8_type, object_ptr, "len_object_type")
            .map_err(|e| crate::error::factory::llvm_build_failed("len object type load", &e))?
            .into_int_value();
        let is_string = builder
            .build_int_compare(
                IntPredicate::EQ,
                object_type,
                i8_type.const_int(1, false),
                "len_is_string",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("len string check", &e))?;
        let is_array = builder
            .build_int_compare(
                IntPredicate::EQ,
                object_type,
                i8_type.const_int(2, false),
                "len_is_array",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("len array check", &e))?;
        let is_dict = builder
            .build_int_compare(
                IntPredicate::EQ,
                object_type,
                i8_type.const_int(3, false),
                "len_is_dict",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("len dict check", &e))?;
        let is_tuple = builder
            .build_int_compare(
                IntPredicate::EQ,
                object_type,
                i8_type.const_int(4, false),
                "len_is_tuple",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("len tuple check", &e))?;
        let string_or_array = builder
            .build_or(is_string, is_array, "len_string_or_array")
            .map_err(|e| crate::error::factory::llvm_build_failed("len collection or", &e))?;
        let dict_or_tuple = builder
            .build_or(is_dict, is_tuple, "len_dict_or_tuple")
            .map_err(|e| crate::error::factory::llvm_build_failed("len collection or", &e))?;
        let is_collection = builder
            .build_or(string_or_array, dict_or_tuple, "len_is_collection")
            .map_err(|e| crate::error::factory::llvm_build_failed("len collection check", &e))?;
        builder
            .build_conditional_branch(is_collection, len_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("len type branch", &e))?;
        let type_loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM len type block missing".to_string()))?;

        builder.position_at_end(len_block);
        let len_ptr = unsafe {
            builder
                .build_gep(i8_type, object_ptr, &[i64_type.const_int(8, false)], "len_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_ptr, "len_value")
            .map_err(|e| crate::error::factory::llvm_build_failed("len load", &e))?
            .into_int_value();
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("len done branch", &e))?;
        let len_loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM len load block missing".to_string()))?;

        builder.position_at_end(done_block);
        let phi = builder
            .build_phi(i64_type, "rt_len_inline")
            .map_err(|e| crate::error::factory::llvm_build_failed("len phi", &e))?;
        phi.add_incoming(&[
            (&invalid, current_block),
            (&invalid, type_loaded_block),
            (&len, len_loaded_block),
        ]);
        vreg_map.insert(dest, phi.as_basic_value());
        Ok(true)
    }

    /// Expand text RuntimeValue arguments to (ptr, len) pairs for SFFI calls.
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
    fn compile_inline_bytes_u8_at(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        trusted_array: bool,
    ) -> Result<bool, CompileError> {
        if args.len() != 2 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let current_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM builder has no insert block for rt_bytes_u8_at".to_string()))?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());

        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();

        let tag_mask = i64_type.const_int(7, false);
        let bounds_block = self.context_ref().append_basic_block(function, "bytes_bounds");
        let load_block = self.context_ref().append_basic_block(function, "bytes_load");
        let done_block = self.context_ref().append_basic_block(function, "bytes_done");
        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "bytes_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "bytes_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes int_to_ptr", &e))?;
        let type_block = if trusted_array {
            builder
                .build_unconditional_branch(bounds_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes bounds branch", &e))?;
            None
        } else {
            let heap_tag = i64_type.const_int(1, false);
            let tag = builder
                .build_and(array, tag_mask, "bytes_tag")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes tag", &e))?;
            let is_heap = builder
                .build_int_compare(IntPredicate::EQ, tag, heap_tag, "bytes_is_heap")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes heap check", &e))?;
            let type_block = self.context_ref().append_basic_block(function, "bytes_type");
            builder
                .build_conditional_branch(is_heap, type_block, done_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes heap branch", &e))?;

            builder.position_at_end(type_block);
            let object_type = builder
                .build_load(i8_type, array_ptr, "bytes_object_type")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes object type load", &e))?
                .into_int_value();
            let is_array = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    object_type,
                    i8_type.const_int(2, false),
                    "bytes_is_array",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes array check", &e))?;
            builder
                .build_conditional_branch(is_array, bounds_block, done_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes type branch", &e))?;
            Some(type_block)
        };

        builder.position_at_end(bounds_block);
        let len_ptr = unsafe {
            builder
                .build_gep(i8_type, array_ptr, &[i64_type.const_int(8, false)], "bytes_len_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_ptr, "bytes_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes len load", &e))?
            .into_int_value();
        let zero = i64_type.const_zero();
        let index_is_negative = builder
            .build_int_compare(IntPredicate::SLT, index, zero, "bytes_index_negative")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes index compare", &e))?;
        let negative_index = builder
            .build_int_add(len, index, "bytes_negative_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes negative index", &e))?;
        let normalized_index = builder
            .build_select(index_is_negative, negative_index, index, "bytes_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes index select", &e))?
            .into_int_value();
        let ge_zero = builder
            .build_int_compare(IntPredicate::SGE, normalized_index, zero, "bytes_ge_zero")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes ge zero", &e))?;
        let lt_len = builder
            .build_int_compare(IntPredicate::SLT, normalized_index, len, "bytes_lt_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes lt len", &e))?;
        let in_bounds = builder
            .build_and(ge_zero, lt_len, "bytes_in_bounds")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes bounds and", &e))?;
        builder
            .build_conditional_branch(in_bounds, load_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes bounds branch", &e))?;

        builder.position_at_end(load_block);
        let data_field_ptr = unsafe {
            builder
                .build_gep(i8_type, array_ptr, &[i64_type.const_int(24, false)], "bytes_data_field")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "bytes_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes data load", &e))?
            .into_pointer_value();
        let packed_block = self.context_ref().append_basic_block(function, "bytes_packed_load");
        let slot_block = self.context_ref().append_basic_block(function, "bytes_slot_load");
        let gc_flags_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(1, false)],
                    "bytes_gc_flags_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes gc flags gep", &e))?
        };
        let gc_flags = builder
            .build_load(i8_type, gc_flags_ptr, "bytes_gc_flags")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes gc flags load", &e))?
            .into_int_value();
        let byte_packed = builder
            .build_and(gc_flags, i8_type.const_int(8, false), "bytes_packed_flag")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed flag", &e))?;
        let is_byte_packed = builder
            .build_int_compare(IntPredicate::NE, byte_packed, i8_type.const_zero(), "bytes_is_packed")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed check", &e))?;
        builder
            .build_conditional_branch(is_byte_packed, packed_block, slot_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed branch", &e))?;

        builder.position_at_end(packed_block);
        let packed_ptr = unsafe {
            builder
                .build_gep(i8_type, data_ptr, &[normalized_index], "bytes_packed_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed gep", &e))?
        };
        let packed_byte = builder
            .build_load(i8_type, packed_ptr, "bytes_packed_byte")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed load", &e))?
            .into_int_value();
        let packed_value = builder
            .build_int_z_extend(packed_byte, i64_type, "bytes_packed_value")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed zext", &e))?;
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes packed done branch", &e))?;
        let packed_loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes packed load block missing".to_string()))?;

        builder.position_at_end(slot_block);
        let elem_ptr = unsafe {
            builder
                .build_gep(i64_type, data_ptr, &[normalized_index], "bytes_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes elem gep", &e))?
        };
        let raw = builder
            .build_load(i64_type, elem_ptr, "bytes_raw")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes raw load", &e))?
            .into_int_value();
        let raw_tag = builder
            .build_and(raw, tag_mask, "bytes_raw_tag")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes raw tag", &e))?;
        let raw_is_int = builder
            .build_int_compare(IntPredicate::EQ, raw_tag, zero, "bytes_raw_is_int")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes raw int check", &e))?;
        let int_payload = builder
            .build_right_shift(raw, i64_type.const_int(3, false), true, "bytes_int_payload")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes int payload", &e))?;
        let int_byte = builder
            .build_and(int_payload, i64_type.const_int(0xff, false), "bytes_int_byte")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes int mask", &e))?;
        let raw_byte = builder
            .build_and(raw, i64_type.const_int(0xff, false), "bytes_raw_byte")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes raw mask", &e))?;
        let value = builder
            .build_select(raw_is_int, int_byte, raw_byte, "bytes_value")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes value select", &e))?
            .into_int_value();
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes done branch", &e))?;
        let loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes load block missing".to_string()))?;

        builder.position_at_end(done_block);
        let phi = builder
            .build_phi(i64_type, "bytes_u8_at")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes phi", &e))?;
        if let Some(type_block) = type_block {
            phi.add_incoming(&[
                (&zero, current_block),
                (&zero, type_block),
                (&zero, bounds_block),
                (&packed_value, packed_loaded_block),
                (&value, loaded_block),
            ]);
        } else {
            phi.add_incoming(&[
                (&zero, bounds_block),
                (&packed_value, packed_loaded_block),
                (&value, loaded_block),
            ]);
        }
        vreg_map.insert(dest, phi.as_basic_value());
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_typed_bytes_le_unchecked(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        width: u64,
    ) -> Result<bool, CompileError> {
        if args.len() != 2 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let ptr_bits = builder
            .build_and(
                array,
                i64_type.const_int(!7u64, false),
                "typed_bytes_unchecked_ptr_bits",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "typed_bytes_unchecked_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked int_to_ptr", &e))?;
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "typed_bytes_unchecked_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "typed_bytes_unchecked_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked data load", &e))?
            .into_pointer_value();
        let ptr = unsafe {
            builder
                .build_gep(i8_type, data_ptr, &[index], "typed_bytes_unchecked_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked gep", &e))?
        };
        let value = if width == 8 {
            let loaded = builder
                .build_load(i64_type, ptr, "typed_bytes_unchecked_u64")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u64 load", &e))?;
            if let Some(inst) = loaded.as_instruction_value() {
                inst.set_alignment(1)
                    .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u64 align", &e))?;
            }
            loaded.into_int_value()
        } else if width == 1 {
            let i8_type = self.context_ref().i8_type();
            let loaded = builder
                .build_load(i8_type, ptr, "typed_bytes_unchecked_u8")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u8 load", &e))?;
            builder
                .build_int_z_extend(loaded.into_int_value(), i64_type, "typed_bytes_unchecked_u8_wide")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u8 zext", &e))?
        } else {
            let i32_type = self.context_ref().i32_type();
            let loaded = builder
                .build_load(i32_type, ptr, "typed_bytes_unchecked_u32")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u32 load", &e))?;
            if let Some(inst) = loaded.as_instruction_value() {
                inst.set_alignment(1)
                    .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u32 align", &e))?;
            }
            builder
                .build_int_z_extend(loaded.into_int_value(), i64_type, "typed_bytes_unchecked_u32_wide")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes unchecked u32 zext", &e))?
        };
        vreg_map.insert(dest, value.into());
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_typed_words_at(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        width: u32,
    ) -> Result<bool, CompileError> {
        if args.len() != 2 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let current_block = builder.get_insert_block().ok_or_else(|| {
            CompileError::semantic("LLVM builder has no insert block for rt_typed_words_at".to_string())
        })?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let zero = i64_type.const_zero();

        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();

        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "typed_words_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "typed_words_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words int_to_ptr", &e))?;
        let len_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(8, false)],
                    "typed_words_len_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed words len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_field_ptr, "typed_words_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words len load", &e))?
            .into_int_value();
        let is_negative = builder
            .build_int_compare(IntPredicate::SLT, index, zero, "typed_words_neg")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words neg compare", &e))?;
        let adjusted = builder
            .build_int_add(len, index, "typed_words_adjusted")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words adjusted", &e))?;
        let normalized = builder
            .build_select(is_negative, adjusted, index, "typed_words_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words select", &e))?
            .into_int_value();
        let lower_ok = builder
            .build_int_compare(IntPredicate::SGE, normalized, zero, "typed_words_lower_ok")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words lower compare", &e))?;
        let upper_ok = builder
            .build_int_compare(IntPredicate::SLT, normalized, len, "typed_words_upper_ok")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words upper compare", &e))?;
        let in_bounds = builder
            .build_and(lower_ok, upper_ok, "typed_words_in_bounds")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words bounds and", &e))?;

        let load_block = self.context_ref().append_basic_block(function, "typed_words_load");
        let done_block = self.context_ref().append_basic_block(function, "typed_words_done");
        builder
            .build_conditional_branch(in_bounds, load_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words bounds branch", &e))?;

        builder.position_at_end(load_block);
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "typed_words_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed words data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "typed_words_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words data load", &e))?
            .into_pointer_value();
        let elem_ptr = unsafe {
            builder
                .build_gep(i64_type, data_ptr, &[normalized], "typed_words_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed words elem gep", &e))?
        };
        let loaded = builder
            .build_load(i64_type, elem_ptr, "typed_words_value")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words value load", &e))?
            .into_int_value();
        let raw_tag = builder
            .build_and(loaded, i64_type.const_int(7, false), "typed_words_raw_tag")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words raw tag", &e))?;
        let raw_is_int = builder
            .build_int_compare(IntPredicate::EQ, raw_tag, zero, "typed_words_raw_is_int")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words raw int compare", &e))?;
        let int_payload = builder
            .build_right_shift(loaded, i64_type.const_int(3, false), true, "typed_words_int_payload")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words int payload", &e))?;
        let value = builder
            .build_select(raw_is_int, int_payload, loaded, "typed_words_runtime_value")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words raw select", &e))?
            .into_int_value();
        let value = if width == 32 {
            builder
                .build_and(value, i64_type.const_int(0xffff_ffff, false), "typed_words_u32_mask")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed words u32 mask", &e))?
        } else {
            value
        };
        let loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM typed words load block missing".to_string()))?;
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words done branch", &e))?;

        builder.position_at_end(done_block);
        let phi = builder
            .build_phi(i64_type, "typed_words_result")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed words phi", &e))?;
        phi.add_incoming(&[(&zero, current_block), (&value, loaded_block)]);
        vreg_map.insert(dest, phi.as_basic_value());
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_adler_reduce(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<bool, CompileError> {
        if args.len() != 1 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let i64_type = self.runtime_int_type();
        let value = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let low_mask = i64_type.const_int(0xFFFF, false);
        let low = builder
            .build_and(value, low_mask, "adler_reduce_low")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce low", &e))?;
        let high = builder
            .build_right_shift(value, i64_type.const_int(16, false), false, "adler_reduce_high")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high", &e))?;
        let high_times_16 = builder
            .build_left_shift(high, i64_type.const_int(4, false), "adler_reduce_high16")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high16", &e))?;
        let high_times_15 = builder
            .build_int_sub(high_times_16, high, "adler_reduce_high15")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high15", &e))?;
        let reduced = builder
            .build_int_add(low, high_times_15, "adler_reduce_sum")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce sum", &e))?;
        let low = builder
            .build_and(reduced, low_mask, "adler_reduce_low2")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce low2", &e))?;
        let high = builder
            .build_right_shift(reduced, i64_type.const_int(16, false), false, "adler_reduce_high2")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high2", &e))?;
        let high_times_16 = builder
            .build_left_shift(high, i64_type.const_int(4, false), "adler_reduce_high16_2")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high16 2", &e))?;
        let high_times_15 = builder
            .build_int_sub(high_times_16, high, "adler_reduce_high15_2")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce high15 2", &e))?;
        let reduced = builder
            .build_int_add(low, high_times_15, "adler_reduce_sum2")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce sum2", &e))?;
        let subtract_modulus = builder
            .build_int_compare(
                IntPredicate::UGE,
                reduced,
                i64_type.const_int(65521, false),
                "adler_reduce_ge_mod",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce compare", &e))?;
        let minus_modulus = builder
            .build_int_sub(reduced, i64_type.const_int(65521, false), "adler_reduce_minus_mod")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce subtract", &e))?;
        let selected = builder
            .build_select(subtract_modulus, minus_modulus, reduced, "adler_reduce_select")
            .map_err(|e| crate::error::factory::llvm_build_failed("adler reduce select", &e))?;
        vreg_map.insert(dest, selected);
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_typed_bytes_le_set_unchecked(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        width: u64,
    ) -> Result<bool, CompileError> {
        if args.len() != 3 {
            return Ok(false);
        }

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let value = self
            .coerce_value_to_type(self.get_vreg(&args[2], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "typed_bytes_set_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "typed_bytes_set_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set int_to_ptr", &e))?;
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "typed_bytes_set_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "typed_bytes_set_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set data load", &e))?
            .into_pointer_value();
        let ptr = unsafe {
            builder
                .build_gep(i8_type, data_ptr, &[index], "typed_bytes_set_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set gep", &e))?
        };
        let store = if width == 8 {
            builder
                .build_store(ptr, value)
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set u64 store", &e))?
        } else {
            let i32_type = self.context_ref().i32_type();
            let narrowed = builder
                .build_int_truncate(value, i32_type, "typed_bytes_set_u32")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set u32 trunc", &e))?;
            builder
                .build_store(ptr, narrowed)
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set u32 store", &e))?
        };
        store
            .set_alignment(1)
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set align", &e))?;
        if let Some(dest) = dest {
            vreg_map.insert(dest, self.context_ref().bool_type().const_int(1, false).into());
        }
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_typed_bytes_le_at(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        width: u64,
    ) -> Result<bool, CompileError> {
        if args.len() != 2 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let current_block = builder.get_insert_block().ok_or_else(|| {
            CompileError::semantic("LLVM builder has no insert block for rt_typed_bytes_le_at".to_string())
        })?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let zero = i64_type.const_zero();

        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "typed_bytes_le_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "typed_bytes_le_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le int_to_ptr", &e))?;

        let load_block = self.context_ref().append_basic_block(function, "typed_bytes_le_load");
        let done_block = self.context_ref().append_basic_block(function, "typed_bytes_le_done");

        let len_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(8, false)],
                    "typed_bytes_le_len_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_ptr, "typed_bytes_le_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le len load", &e))?
            .into_int_value();
        let ge_zero = builder
            .build_int_compare(IntPredicate::SGE, index, zero, "typed_bytes_le_ge_zero")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le ge zero", &e))?;
        let end = builder
            .build_int_add(index, i64_type.const_int(width, false), "typed_bytes_le_end")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le end", &e))?;
        let le_len = builder
            .build_int_compare(IntPredicate::SLE, end, len, "typed_bytes_le_in_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le len check", &e))?;
        let in_bounds = builder
            .build_and(ge_zero, le_len, "typed_bytes_le_in_bounds")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le bounds and", &e))?;
        builder
            .build_conditional_branch(in_bounds, load_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le bounds branch", &e))?;

        builder.position_at_end(load_block);
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "typed_bytes_le_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "typed_bytes_le_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le data load", &e))?
            .into_pointer_value();
        let ptr = unsafe {
            builder
                .build_gep(i8_type, data_ptr, &[index], "typed_bytes_le_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le gep", &e))?
        };
        let value = if width == 8 {
            let loaded = builder
                .build_load(i64_type, ptr, "typed_bytes_le_u64")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le u64 load", &e))?;
            if let Some(inst) = loaded.as_instruction_value() {
                inst.set_alignment(1)
                    .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le u64 align", &e))?;
            }
            loaded.into_int_value()
        } else {
            let i32_type = self.context_ref().i32_type();
            let loaded = builder
                .build_load(i32_type, ptr, "typed_bytes_le_u32")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le u32 load", &e))?;
            if let Some(inst) = loaded.as_instruction_value() {
                inst.set_alignment(1)
                    .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le u32 align", &e))?;
            }
            builder
                .build_int_z_extend(loaded.into_int_value(), i64_type, "typed_bytes_le_u32_wide")
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le u32 zext", &e))?
        };
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le done branch", &e))?;
        let loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM typed bytes le block missing".to_string()))?;

        builder.position_at_end(done_block);
        let phi = builder
            .build_phi(i64_type, "typed_bytes_le_at")
            .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes le phi", &e))?;
        phi.add_incoming(&[(&zero, current_block), (&value, loaded_block)]);
        vreg_map.insert(dest, phi.as_basic_value());
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_bytes_le_at(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        width: u64,
    ) -> Result<bool, CompileError> {
        if args.len() != 2 {
            return Ok(false);
        }
        let Some(dest) = dest else {
            return Ok(false);
        };

        let current_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM builder has no insert block for rt_bytes_le_at".to_string()))?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let zero = i64_type.const_zero();
        let tag_mask = i64_type.const_int(7, false);

        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();

        let type_block = self.context_ref().append_basic_block(function, "bytes_le_type");
        let bounds_block = self.context_ref().append_basic_block(function, "bytes_le_bounds");
        let load_block = self.context_ref().append_basic_block(function, "bytes_le_load");
        let packed_block = self.context_ref().append_basic_block(function, "bytes_le_packed");
        let slot_block = self.context_ref().append_basic_block(function, "bytes_le_slots");
        let done_block = self.context_ref().append_basic_block(function, "bytes_le_done");

        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "bytes_le_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "bytes_le_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le int_to_ptr", &e))?;
        let tag = builder
            .build_and(array, tag_mask, "bytes_le_tag")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le tag", &e))?;
        let is_heap = builder
            .build_int_compare(IntPredicate::EQ, tag, i64_type.const_int(1, false), "bytes_le_is_heap")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le heap check", &e))?;
        builder
            .build_conditional_branch(is_heap, type_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le heap branch", &e))?;

        builder.position_at_end(type_block);
        let object_type = builder
            .build_load(i8_type, array_ptr, "bytes_le_object_type")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le object type load", &e))?
            .into_int_value();
        let is_array = builder
            .build_int_compare(
                IntPredicate::EQ,
                object_type,
                i8_type.const_int(2, false),
                "bytes_le_is_array",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le array check", &e))?;
        builder
            .build_conditional_branch(is_array, bounds_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le type branch", &e))?;

        builder.position_at_end(bounds_block);
        let len_ptr = unsafe {
            builder
                .build_gep(i8_type, array_ptr, &[i64_type.const_int(8, false)], "bytes_le_len_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_ptr, "bytes_le_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le len load", &e))?
            .into_int_value();
        let index_is_negative = builder
            .build_int_compare(IntPredicate::SLT, index, zero, "bytes_le_index_negative")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le index compare", &e))?;
        let negative_index = builder
            .build_int_add(len, index, "bytes_le_negative_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le negative index", &e))?;
        let normalized_index = builder
            .build_select(index_is_negative, negative_index, index, "bytes_le_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le index select", &e))?
            .into_int_value();
        let ge_zero = builder
            .build_int_compare(IntPredicate::SGE, normalized_index, zero, "bytes_le_ge_zero")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le ge zero", &e))?;
        let end = builder
            .build_int_add(normalized_index, i64_type.const_int(width, false), "bytes_le_end")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le end", &e))?;
        let le_len = builder
            .build_int_compare(IntPredicate::SLE, end, len, "bytes_le_in_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le len check", &e))?;
        let in_bounds = builder
            .build_and(ge_zero, le_len, "bytes_le_in_bounds")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le bounds and", &e))?;
        builder
            .build_conditional_branch(in_bounds, load_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le bounds branch", &e))?;

        builder.position_at_end(load_block);
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "bytes_le_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "bytes_le_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le data load", &e))?
            .into_pointer_value();
        let gc_flags_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(1, false)],
                    "bytes_le_gc_flags_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le gc flags gep", &e))?
        };
        let gc_flags = builder
            .build_load(i8_type, gc_flags_ptr, "bytes_le_gc_flags")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le gc flags load", &e))?
            .into_int_value();
        let byte_packed = builder
            .build_and(gc_flags, i8_type.const_int(8, false), "bytes_le_packed_flag")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed flag", &e))?;
        let is_byte_packed = builder
            .build_int_compare(
                IntPredicate::NE,
                byte_packed,
                i8_type.const_zero(),
                "bytes_le_is_packed",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed check", &e))?;
        builder
            .build_conditional_branch(is_byte_packed, packed_block, slot_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed branch", &e))?;

        builder.position_at_end(packed_block);
        let mut packed_value = zero;
        for offset in 0..width {
            let elem_index = builder
                .build_int_add(
                    normalized_index,
                    i64_type.const_int(offset, false),
                    "bytes_le_packed_index",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed index", &e))?;
            let ptr = unsafe {
                builder
                    .build_gep(i8_type, data_ptr, &[elem_index], "bytes_le_packed_elem")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed gep", &e))?
            };
            let byte = builder
                .build_load(i8_type, ptr, "bytes_le_packed_byte")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed load", &e))?
                .into_int_value();
            let widened = builder
                .build_int_z_extend(byte, i64_type, "bytes_le_packed_wide")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed zext", &e))?;
            let shifted = if offset == 0 {
                widened
            } else {
                builder
                    .build_left_shift(widened, i64_type.const_int(offset * 8, false), "bytes_le_packed_shift")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed shift", &e))?
            };
            packed_value = builder
                .build_or(packed_value, shifted, "bytes_le_packed_acc")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed or", &e))?;
        }
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le packed done branch", &e))?;
        let packed_loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes le packed block missing".to_string()))?;

        builder.position_at_end(slot_block);
        let mut slot_value = zero;
        for offset in 0..width {
            let elem_index = builder
                .build_int_add(
                    normalized_index,
                    i64_type.const_int(offset, false),
                    "bytes_le_slot_index",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le slot index", &e))?;
            let elem_ptr = unsafe {
                builder
                    .build_gep(i64_type, data_ptr, &[elem_index], "bytes_le_slot_elem")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bytes le slot gep", &e))?
            };
            let raw = builder
                .build_load(i64_type, elem_ptr, "bytes_le_raw")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le raw load", &e))?
                .into_int_value();
            let raw_tag = builder
                .build_and(raw, tag_mask, "bytes_le_raw_tag")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le raw tag", &e))?;
            let raw_is_int = builder
                .build_int_compare(IntPredicate::EQ, raw_tag, zero, "bytes_le_raw_is_int")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le raw int check", &e))?;
            let int_payload = builder
                .build_right_shift(raw, i64_type.const_int(3, false), true, "bytes_le_int_payload")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le int payload", &e))?;
            let int_byte = builder
                .build_and(int_payload, i64_type.const_int(0xff, false), "bytes_le_int_byte")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le int mask", &e))?;
            let raw_byte = builder
                .build_and(raw, i64_type.const_int(0xff, false), "bytes_le_raw_byte")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le raw mask", &e))?;
            let byte = builder
                .build_select(raw_is_int, int_byte, raw_byte, "bytes_le_byte")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le byte select", &e))?
                .into_int_value();
            let shifted = if offset == 0 {
                byte
            } else {
                builder
                    .build_left_shift(byte, i64_type.const_int(offset * 8, false), "bytes_le_slot_shift")
                    .map_err(|e| crate::error::factory::llvm_build_failed("bytes le slot shift", &e))?
            };
            slot_value = builder
                .build_or(slot_value, shifted, "bytes_le_slot_acc")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes le slot or", &e))?;
        }
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le slot done branch", &e))?;
        let slot_loaded_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes le slot block missing".to_string()))?;

        builder.position_at_end(done_block);
        let phi = builder
            .build_phi(i64_type, "bytes_le_at")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes le phi", &e))?;
        phi.add_incoming(&[
            (&zero, current_block),
            (&zero, type_block),
            (&zero, bounds_block),
            (&packed_value, packed_loaded_block),
            (&slot_value, slot_loaded_block),
        ]);
        vreg_map.insert(dest, phi.as_basic_value());
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_inline_bytes_u8_set(
        &self,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        trusted_array: bool,
    ) -> Result<bool, CompileError> {
        if args.len() != 3 {
            return Ok(false);
        }

        let current_block = builder.get_insert_block().ok_or_else(|| {
            CompileError::semantic("LLVM builder has no insert block for rt_bytes_u8_set".to_string())
        })?;
        let function = current_block
            .get_parent()
            .ok_or_else(|| CompileError::semantic("LLVM insert block has no parent function".to_string()))?;

        let i64_type = self.runtime_int_type();
        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());

        let array = self
            .coerce_value_to_type(self.get_vreg(&args[0], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let index = self
            .coerce_value_to_type(self.get_vreg(&args[1], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();
        let value = self
            .coerce_value_to_type(self.get_vreg(&args[2], vreg_map)?, Some(i64_type.into()), builder)?
            .into_int_value();

        let tag_mask = i64_type.const_int(7, false);
        let bounds_block = self.context_ref().append_basic_block(function, "bytes_set_bounds");
        let store_block = self.context_ref().append_basic_block(function, "bytes_set_store");
        let done_block = self.context_ref().append_basic_block(function, "bytes_set_done");
        let ptr_bits = builder
            .build_and(array, i64_type.const_int(!7u64, false), "bytes_set_ptr_bits")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set ptr bits", &e))?;
        let array_ptr = builder
            .build_int_to_ptr(ptr_bits, ptr_type, "bytes_set_array_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set int_to_ptr", &e))?;
        let type_block = if trusted_array {
            builder
                .build_unconditional_branch(bounds_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("typed bytes set bounds branch", &e))?;
            None
        } else {
            let heap_tag = i64_type.const_int(1, false);
            let tag = builder
                .build_and(array, tag_mask, "bytes_set_tag")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set tag", &e))?;
            let is_heap = builder
                .build_int_compare(IntPredicate::EQ, tag, heap_tag, "bytes_set_is_heap")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set heap check", &e))?;
            let type_block = self.context_ref().append_basic_block(function, "bytes_set_type");
            builder
                .build_conditional_branch(is_heap, type_block, done_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set heap branch", &e))?;

            builder.position_at_end(type_block);
            let object_type = builder
                .build_load(i8_type, array_ptr, "bytes_set_object_type")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set object type load", &e))?
                .into_int_value();
            let is_array = builder
                .build_int_compare(
                    IntPredicate::EQ,
                    object_type,
                    i8_type.const_int(2, false),
                    "bytes_set_is_array",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set array check", &e))?;
            builder
                .build_conditional_branch(is_array, bounds_block, done_block)
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set type branch", &e))?;
            Some(type_block)
        };

        builder.position_at_end(bounds_block);
        let len_ptr = unsafe {
            builder
                .build_gep(i8_type, array_ptr, &[i64_type.const_int(8, false)], "bytes_set_len_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set len gep", &e))?
        };
        let len = builder
            .build_load(i64_type, len_ptr, "bytes_set_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set len load", &e))?
            .into_int_value();
        let zero = i64_type.const_zero();
        let index_is_negative = builder
            .build_int_compare(IntPredicate::SLT, index, zero, "bytes_set_index_negative")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set index compare", &e))?;
        let negative_index = builder
            .build_int_add(len, index, "bytes_set_negative_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set negative index", &e))?;
        let normalized_index = builder
            .build_select(index_is_negative, negative_index, index, "bytes_set_index")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set index select", &e))?
            .into_int_value();
        let ge_zero = builder
            .build_int_compare(IntPredicate::SGE, normalized_index, zero, "bytes_set_ge_zero")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set ge zero", &e))?;
        let lt_len = builder
            .build_int_compare(IntPredicate::SLT, normalized_index, len, "bytes_set_lt_len")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set lt len", &e))?;
        let in_bounds = builder
            .build_and(ge_zero, lt_len, "bytes_set_in_bounds")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set bounds and", &e))?;
        builder
            .build_conditional_branch(in_bounds, store_block, done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set bounds branch", &e))?;

        builder.position_at_end(store_block);
        let data_field_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(24, false)],
                    "bytes_set_data_field",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set data gep", &e))?
        };
        let data_ptr = builder
            .build_load(ptr_type, data_field_ptr, "bytes_set_data")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set data load", &e))?
            .into_pointer_value();
        let byte = builder
            .build_and(value, i64_type.const_int(0xff, false), "bytes_set_byte")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set byte mask", &e))?;
        let packed_block = self
            .context_ref()
            .append_basic_block(function, "bytes_set_packed_store");
        let slot_block = self.context_ref().append_basic_block(function, "bytes_set_slot_store");
        let gc_flags_ptr = unsafe {
            builder
                .build_gep(
                    i8_type,
                    array_ptr,
                    &[i64_type.const_int(1, false)],
                    "bytes_set_gc_flags_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set gc flags gep", &e))?
        };
        let gc_flags = builder
            .build_load(i8_type, gc_flags_ptr, "bytes_set_gc_flags")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set gc flags load", &e))?
            .into_int_value();
        let byte_packed = builder
            .build_and(gc_flags, i8_type.const_int(8, false), "bytes_set_packed_flag")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed flag", &e))?;
        let is_byte_packed = builder
            .build_int_compare(
                IntPredicate::NE,
                byte_packed,
                i8_type.const_zero(),
                "bytes_set_is_packed",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed check", &e))?;
        builder
            .build_conditional_branch(is_byte_packed, packed_block, slot_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed branch", &e))?;

        builder.position_at_end(packed_block);
        let packed_ptr = unsafe {
            builder
                .build_gep(i8_type, data_ptr, &[normalized_index], "bytes_set_packed_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed gep", &e))?
        };
        let byte_value = builder
            .build_int_truncate(byte, i8_type, "bytes_set_packed_byte")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed trunc", &e))?;
        builder
            .build_store(packed_ptr, byte_value)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed store", &e))?;
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set packed done branch", &e))?;
        let packed_stored_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes set packed block missing".to_string()))?;

        builder.position_at_end(slot_block);
        let elem_ptr = unsafe {
            builder
                .build_gep(i64_type, data_ptr, &[normalized_index], "bytes_set_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set elem gep", &e))?
        };
        let tagged = builder
            .build_left_shift(byte, i64_type.const_int(3, false), "bytes_set_tagged_int")
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set tagged int", &e))?;
        builder
            .build_store(elem_ptr, tagged)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set store", &e))?;
        builder
            .build_unconditional_branch(done_block)
            .map_err(|e| crate::error::factory::llvm_build_failed("bytes set done branch", &e))?;
        let stored_block = builder
            .get_insert_block()
            .ok_or_else(|| CompileError::semantic("LLVM bytes set block missing".to_string()))?;

        builder.position_at_end(done_block);
        if let Some(dest) = dest {
            let false_value = i64_type.const_int(19, false);
            let true_value = i64_type.const_int(11, false);
            let phi = builder
                .build_phi(i64_type, "bytes_u8_set")
                .map_err(|e| crate::error::factory::llvm_build_failed("bytes set phi", &e))?;
            if let Some(type_block) = type_block {
                phi.add_incoming(&[
                    (&false_value, current_block),
                    (&false_value, type_block),
                    (&false_value, bounds_block),
                    (&true_value, packed_stored_block),
                    (&true_value, stored_block),
                ]);
            } else {
                phi.add_incoming(&[
                    (&false_value, bounds_block),
                    (&true_value, packed_stored_block),
                    (&true_value, stored_block),
                ]);
            }
            vreg_map.insert(dest, phi.as_basic_value());
        }
        Ok(true)
    }

    #[cfg(feature = "llvm")]
    fn compile_simple_runtime_memory_intrinsic(
        &self,
        name: &str,
        dest: Option<crate::mir::VReg>,
        args: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<bool, CompileError> {
        let intrinsic = name.rsplit_once("__").map(|(_, tail)| tail).unwrap_or(name);
        if !matches!(
            intrinsic,
            "spl_load_i64" | "spl_store_i64" | "spl_load_u8" | "spl_store_u8" | "spl_f64_to_bits"
        ) {
            return Ok(false);
        }

        let i64_type = self.runtime_int_type();
        if intrinsic == "spl_f64_to_bits" {
            if args.len() != 1 {
                return Err(crate::error::factory::llvm_build_failed(
                    "simple runtime f64 bitcast intrinsic",
                    &format!("{intrinsic} expects 1 args, got {}", args.len()),
                ));
            }
            if let Some(d) = dest {
                let value = self.get_vreg(&args[0], vreg_map)?;
                let bits = self.coerce_value_to_type(value, Some(i64_type.into()), builder)?;
                vreg_map.insert(d, bits);
            }
            return Ok(true);
        }

        let expected_args = if intrinsic.starts_with("spl_load_") { 2 } else { 3 };
        if args.len() != expected_args {
            return Err(crate::error::factory::llvm_build_failed(
                "simple runtime memory intrinsic",
                &format!("{intrinsic} expects {expected_args} args, got {}", args.len()),
            ));
        }

        let i8_type = self.context_ref().i8_type();
        let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let base = self.get_vreg(&args[0], vreg_map)?;
        let base = self
            .coerce_value_to_type(base, Some(i64_type.into()), builder)?
            .into_int_value();
        let offset = self.get_vreg(&args[1], vreg_map)?;
        let offset = self
            .coerce_value_to_type(offset, Some(i64_type.into()), builder)?
            .into_int_value();
        let base_ptr = builder
            .build_int_to_ptr(base, ptr_type, "spl_mem_base")
            .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime memory int_to_ptr", &e))?;
        let addr = unsafe {
            builder
                .build_gep(i8_type, base_ptr, &[offset], "spl_mem_addr")
                .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime memory gep", &e))?
        };

        match intrinsic {
            "spl_load_i64" => {
                let loaded = builder
                    .build_load(i64_type, addr, "spl_load_i64")
                    .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime load_i64", &e))?;
                if let Some(d) = dest {
                    vreg_map.insert(d, loaded);
                }
            }
            "spl_load_u8" => {
                let loaded = builder
                    .build_load(i8_type, addr, "spl_load_u8")
                    .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime load_u8", &e))?
                    .into_int_value();
                let widened = builder
                    .build_int_z_extend(loaded, i64_type, "spl_load_u8_zext")
                    .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime load_u8 zext", &e))?;
                if let Some(d) = dest {
                    vreg_map.insert(d, widened.into());
                }
            }
            "spl_store_i64" | "spl_store_u8" => {
                let value = self.get_vreg(&args[2], vreg_map)?;
                let value = self
                    .coerce_value_to_type(value, Some(i64_type.into()), builder)?
                    .into_int_value();
                let store_value: inkwell::values::BasicValueEnum = if intrinsic == "spl_store_u8" {
                    builder
                        .build_int_truncate(value, i8_type, "spl_store_u8_trunc")
                        .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime store_u8 trunc", &e))?
                        .into()
                } else {
                    value.into()
                };
                builder
                    .build_store(addr, store_value)
                    .map_err(|e| crate::error::factory::llvm_build_failed("simple runtime store", &e))?;
                if let Some(d) = dest {
                    vreg_map.insert(d, i64_type.const_int(0, false).into());
                }
            }
            _ => unreachable!(),
        }

        Ok(true)
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
        let sffi_name = map_sffi_name(func_name_raw);
        let i64_type = self.runtime_int_type();

        if sffi_name == "rt_typed_bytes_u8_at"
            && self.compile_inline_bytes_u8_at(dest, args, vreg_map, builder, true)?
        {
            return Ok(());
        }
        if sffi_name == "rt_bytes_u8_at" && self.compile_inline_bytes_u8_at(dest, args, vreg_map, builder, false)? {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u32_le_at"
            && self.compile_inline_typed_bytes_le_unchecked(dest, args, vreg_map, builder, 4)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u64_le_at"
            && self.compile_inline_typed_bytes_le_unchecked(dest, args, vreg_map, builder, 8)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u32_le_unchecked"
            && self.compile_inline_typed_bytes_le_unchecked(dest, args, vreg_map, builder, 4)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u64_le_unchecked"
            && self.compile_inline_typed_bytes_le_unchecked(dest, args, vreg_map, builder, 8)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u8_unchecked"
            && self.compile_inline_typed_bytes_le_unchecked(dest, args, vreg_map, builder, 1)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_words_u32_at"
            && self.compile_inline_typed_words_at(dest, args, vreg_map, builder, 32)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_words_u64_at"
            && self.compile_inline_typed_words_at(dest, args, vreg_map, builder, 64)?
        {
            return Ok(());
        }
        if sffi_name == "_adler_reduce" && self.compile_inline_adler_reduce(dest, args, vreg_map, builder)? {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u32_le_set"
            && self.compile_inline_typed_bytes_le_set_unchecked(dest, args, vreg_map, builder, 4)?
        {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u64_le_set"
            && self.compile_inline_typed_bytes_le_set_unchecked(dest, args, vreg_map, builder, 8)?
        {
            return Ok(());
        }
        if sffi_name == "rt_bytes_u32_le_at" && self.compile_inline_bytes_le_at(dest, args, vreg_map, builder, 4)? {
            return Ok(());
        }
        if sffi_name == "rt_bytes_u64_le_at" && self.compile_inline_bytes_le_at(dest, args, vreg_map, builder, 8)? {
            return Ok(());
        }
        if sffi_name == "rt_typed_bytes_u8_set"
            && self.compile_inline_bytes_u8_set(dest, args, vreg_map, builder, true)?
        {
            return Ok(());
        }
        if sffi_name == "rt_bytes_u8_set" && self.compile_inline_bytes_u8_set(dest, args, vreg_map, builder, false)? {
            return Ok(());
        }

        if matches!(sffi_name, "rt_len" | "rt_array_len")
            && self.compile_inline_len(dest, args, vreg_map, builder, sffi_name == "rt_array_len")?
        {
            return Ok(());
        }

        if self.compile_simple_runtime_memory_intrinsic(func_name_raw, dest, args, vreg_map, builder)? {
            return Ok(());
        }

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
            "char_code_at" => Some("rt_string_char_code_at"),
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
            "unwrap" | "unwrap_or" | "unwrap_err" => Some("rt_enum_payload"),
            _ => None,
        };

        if let Some(rt_fn_name) = bare_rt_redirect {
            let needs_receiver = !matches!(rt_fn_name, "rt_enum_payload" | "rt_enum_check_discriminant");
            if needs_receiver && args.is_empty() {
                return Err(crate::error::factory::llvm_build_failed(
                    "rt redirect call",
                    &format!("missing receiver for runtime redirect {}", rt_fn_name),
                ));
            }
            if matches!(rt_fn_name, "rt_len" | "rt_array_len")
                && self.compile_inline_len(dest, args, vreg_map, builder, rt_fn_name == "rt_array_len")?
            {
                return Ok(());
            }
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
                self.context_ref().bool_type().fn_type(&param_types, false)
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

        let qualified_name = func_name_raw.replace("_dot_", ".");
        if let Some(dot_pos) = qualified_name.rfind('.') {
            let method = &qualified_name[dot_pos + 1..];

            if matches!(method, "min" | "max") && args.len() >= 2 {
                let lhs = self.get_vreg(&args[0], vreg_map)?;
                let rhs = self.get_vreg(&args[1], vreg_map)?;
                let lhs = self.coerce_value_to_type(lhs, Some(i64_type.into()), builder)?;
                let rhs = self.coerce_value_to_type(rhs, Some(i64_type.into()), builder)?;
                let lhs = lhs.into_int_value();
                let rhs = rhs.into_int_value();
                let pred = if method == "min" {
                    inkwell::IntPredicate::SLE
                } else {
                    inkwell::IntPredicate::SGE
                };
                let cmp = builder
                    .build_int_compare(pred, lhs, rhs, "call_int_minmax_cmp")
                    .map_err(|e| crate::error::factory::llvm_build_failed("qualified int min/max compare", &e))?;
                let selected = builder
                    .build_select(cmp, lhs, rhs, "call_int_minmax_select")
                    .map_err(|e| crate::error::factory::llvm_build_failed("qualified int min/max select", &e))?;
                if let Some(d) = dest {
                    vreg_map.insert(d, selected);
                }
                return Ok(());
            }

            if matches!(method, "chr" | "to_char") && !args.is_empty() {
                let recv = self.get_vreg(&args[0], vreg_map)?;
                let recv = self.coerce_value_to_type(recv, Some(i64_type.into()), builder)?;
                let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                let rt_func = module
                    .get_function("char_from_code")
                    .unwrap_or_else(|| module.add_function("char_from_code", fn_type, None));
                let call_site = builder
                    .build_call(rt_func, &[recv.into()], "qualified_char_from_code")
                    .map_err(|e| crate::error::factory::llvm_build_failed("qualified char_from_code call", &e))?;
                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(d, ret_val);
                    }
                }
                return Ok(());
            }

            let qualified_rt_redirect: Option<&str> = match method {
                "starts_with" => Some("rt_string_starts_with"),
                "ends_with" => Some("rt_string_ends_with"),
                "contains" | "contains_key" | "has_key" => Some("rt_contains"),
                "split" => Some("rt_string_split"),
                "trim" => Some("rt_string_trim"),
                "repeat" => Some("lib__common__string_core__str_repeat"),
                "replace" => Some("rt_string_replace"),
                "to_upper" | "upper" => Some("rt_string_to_upper"),
                "to_lower" | "lower" => Some("rt_string_to_lower"),
                "char_at" | "at" => Some("rt_string_char_at"),
                "char_code_at" => Some("rt_string_char_code_at"),
                "to_text" | "to_string" | "str" => Some("rt_to_string"),
                "to_int" | "to_i64" | "parse_int" => Some("rt_string_to_int"),
                "to_float" | "to_f64" | "parse_float" | "parse_f64" | "parse_f64_safe" => Some("rt_string_to_float"),
                "concat" => Some("rt_string_concat"),
                "rfind" | "last_index_of" => Some("rt_string_rfind"),
                "push" => Some("rt_array_push"),
                "pop" => Some("rt_array_pop"),
                "sort" => Some("rt_array_sort"),
                "reverse" => Some("rt_array_reverse"),
                "clear" => Some("rt_array_clear"),
                "slice" => Some("rt_slice"),
                "len" => Some("rt_len"),
                "get" => Some("rt_index_get"),
                "set" => Some("rt_index_set"),
                "keys" => Some("rt_dict_keys"),
                "values" => Some("rt_dict_values"),
                "unwrap" | "unwrap_or" | "unwrap_err" => Some("rt_enum_payload"),
                "is_none" => Some("rt_is_none"),
                "is_some" => Some("rt_is_some"),
                "is_ok" | "is_err" => Some("rt_enum_check_discriminant"),
                _ => None,
            };

            if let Some(rt_fn_name) = qualified_rt_redirect {
                let expected_arity = qualified_runtime_arity(method, rt_fn_name);
                if expected_arity == Some(args.len()) {
                    if matches!(rt_fn_name, "rt_len" | "rt_array_len")
                        && self.compile_inline_len(dest, args, vreg_map, builder, rt_fn_name == "rt_array_len")?
                    {
                        return Ok(());
                    }
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
                        "rt_array_push"
                            | "rt_array_clear"
                            | "rt_array_reverse"
                            | "rt_array_sort"
                            | "rt_index_set"
                            | "rt_contains"
                            | "rt_is_none"
                            | "rt_is_some"
                            | "rt_enum_check_discriminant"
                    );
                    let fn_type = if returns_bool {
                        self.context_ref().bool_type().fn_type(&param_types, false)
                    } else {
                        i64_type.fn_type(&param_types, false)
                    };
                    let rt_func = module
                        .get_function(rt_fn_name)
                        .unwrap_or_else(|| module.add_function(rt_fn_name, fn_type, None));
                    let call_site = builder
                        .build_call(rt_func, &arg_vals, "qualified_rt_redirect")
                        .map_err(|e| crate::error::factory::llvm_build_failed("qualified rt redirect call", &e))?;
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
            }
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
        let direct_method_name = resolved_dotted
            .rsplit('.')
            .next()
            .or_else(|| raw_dotted.rsplit('.').next());

        if let Some(method_name) = direct_method_name {
            if matches!(method_name, "unwrap" | "unwrap_err") && args.len() == 1 {
                let rt_func = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function("rt_enum_payload", fn_type, None)
                });
                let recv = self.get_vreg(&args[0], vreg_map)?;
                let recv = self.coerce_value_to_type(recv, Some(i64_type.into()), builder)?;
                let call_site = builder
                    .build_call(rt_func, &[recv.into()], "direct_enum_payload")
                    .map_err(|e| crate::error::factory::llvm_build_failed("direct enum payload call", &e))?;
                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        vreg_map.insert(d, ret_val);
                    } else {
                        vreg_map.insert(d, i64_type.const_int(0, false).into());
                    }
                }
                return Ok(());
            }

            if matches!(method_name, "is_ok" | "is_err") && args.len() == 1 {
                let rt_func = module.get_function("rt_enum_check_discriminant").unwrap_or_else(|| {
                    let fn_type = self
                        .context_ref()
                        .bool_type()
                        .fn_type(&[i64_type.into(), i64_type.into()], false);
                    module.add_function("rt_enum_check_discriminant", fn_type, None)
                });
                let recv = self.get_vreg(&args[0], vreg_map)?;
                let recv = self.coerce_value_to_type(recv, Some(i64_type.into()), builder)?;
                let variant = if method_name == "is_ok" { "Ok" } else { "Err" };
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                use std::hash::{Hash, Hasher};
                variant.hash(&mut hasher);
                let disc = i64_type.const_int(hasher.finish() & 0xFFFF_FFFF, false);
                let call_site = builder
                    .build_call(rt_func, &[recv.into(), disc.into()], "direct_enum_disc")
                    .map_err(|e| crate::error::factory::llvm_build_failed("direct enum discriminant call", &e))?;
                if let Some(d) = dest {
                    if let Some(ret_val) = call_site.try_as_basic_value().left() {
                        let ret_val = self.coerce_value_to_type(ret_val, Some(i64_type.into()), builder)?;
                        vreg_map.insert(d, ret_val);
                    } else {
                        vreg_map.insert(d, i64_type.const_int(0, false).into());
                    }
                }
                return Ok(());
            }
        }

        // Get or declare the called function (with suffix matching safety net)
        let called_func = module
            .get_function(sffi_name)
            .or_else(|| module.get_function(resolved_name))
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

        // Expand text RuntimeValue arguments to (ptr, len) pairs for SFFI calls.
        // This handles the ABI mismatch between Simple (text = RuntimeValue i64)
        // and Rust SFFI (text = *const u8 + u64 len).
        let arg_vals: Vec<inkwell::values::BasicMetadataValueEnum> =
            if let Some(text_indices) = crate::codegen::instr::calls::text_arg_indices(sffi_name) {
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

        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());

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
            let ptr_slot_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());

            let offset_val = self.context_ref().i32_type().const_int(0, false);
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
                    self.context_ref().void_type().fn_type(&llvm_param_types, false)
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
        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
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
        let name_const = self.context_ref().const_string(name_bytes, false);
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
                let offset = self
                    .context_ref()
                    .i32_type()
                    .const_int((index as u64) * slot_bytes, false);
                let slot_ptr = unsafe { builder.build_gep(i8_type, argv_ptr, &[offset], "interp_argv_slot") }
                    .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
                let typed_ptr = builder
                    .build_pointer_cast(
                        slot_ptr,
                        self.context_ref().ptr_type(inkwell::AddressSpace::default()),
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
