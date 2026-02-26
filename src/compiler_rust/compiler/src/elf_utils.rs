//! ELF object file parsing and relocation utilities.

use simple_runtime::value;

/// Helper to extract a null-terminated section name from the string table.
#[inline]
pub(crate) fn get_section_name(shstrtab: &[u8], sh_name: usize) -> Option<&str> {
    if sh_name >= shstrtab.len() {
        return None;
    }
    let name_end = shstrtab[sh_name..]
        .iter()
        .position(|&c| c == 0)
        .unwrap_or(shstrtab.len() - sh_name);
    std::str::from_utf8(&shstrtab[sh_name..sh_name + name_end]).ok()
}

/// Extract code from an object file.
/// Tries to parse as ELF and extract .text section, with relocation support.
pub(crate) fn extract_code_from_object(object_code: &[u8]) -> Vec<u8> {
    // Try to parse as ELF and extract .text section
    if object_code.len() > 4 && &object_code[0..4] == b"\x7fELF" {
        // This is ELF format - try to extract .text
        if let Some(text) = extract_elf_text_section(object_code) {
            return text;
        }
    }

    // Fallback: assume it's raw code or return a stub
    // Return a simple "mov eax, 0; ret" as fallback
    vec![0xB8, 0x00, 0x00, 0x00, 0x00, 0xC3]
}

/// Parse ELF object file, extract .text section, and apply relocations.
pub(crate) fn extract_elf_text_section(elf_data: &[u8]) -> Option<Vec<u8>> {
    // Minimal ELF64 parsing to extract .text section
    if elf_data.len() < 64 {
        return None;
    }

    // Check ELF magic
    if &elf_data[0..4] != b"\x7fELF" {
        return None;
    }

    // ELF64 header fields
    let e_shoff = u64::from_le_bytes(elf_data[40..48].try_into().ok()?) as usize;
    let e_shentsize = u16::from_le_bytes(elf_data[58..60].try_into().ok()?) as usize;
    let e_shnum = u16::from_le_bytes(elf_data[60..62].try_into().ok()?) as usize;
    let e_shstrndx = u16::from_le_bytes(elf_data[62..64].try_into().ok()?) as usize;

    if e_shoff == 0 || e_shnum == 0 {
        return None;
    }

    // Find section header string table
    let shstrtab_hdr_offset = e_shoff + e_shstrndx * e_shentsize;
    if shstrtab_hdr_offset + e_shentsize > elf_data.len() {
        return None;
    }
    let shstrtab_offset = u64::from_le_bytes(
        elf_data[shstrtab_hdr_offset + 24..shstrtab_hdr_offset + 32]
            .try_into()
            .ok()?,
    ) as usize;
    let shstrtab_size = u64::from_le_bytes(
        elf_data[shstrtab_hdr_offset + 32..shstrtab_hdr_offset + 40]
            .try_into()
            .ok()?,
    ) as usize;

    if shstrtab_offset + shstrtab_size > elf_data.len() {
        return None;
    }
    let shstrtab = &elf_data[shstrtab_offset..shstrtab_offset + shstrtab_size];

    // Parse all sections to find .text, .rela.text, .symtab, and .strtab
    let mut text_section: Option<(usize, usize)> = None;
    let mut rela_text_section: Option<(usize, usize)> = None;
    let mut symtab_section: Option<(usize, usize, usize)> = None; // (offset, size, link)
    let mut strtab_offset: Option<usize> = None;

    for i in 0..e_shnum {
        let sh_offset = e_shoff + i * e_shentsize;
        if sh_offset + e_shentsize > elf_data.len() {
            continue;
        }

        let sh_name = u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().ok()?) as usize;
        let sh_type = u32::from_le_bytes(elf_data[sh_offset + 4..sh_offset + 8].try_into().ok()?);
        let sh_link = u32::from_le_bytes(elf_data[sh_offset + 40..sh_offset + 44].try_into().ok()?);

        // Get section name from string table
        if let Some(name) = get_section_name(shstrtab, sh_name) {
            let offset = u64::from_le_bytes(elf_data[sh_offset + 24..sh_offset + 32].try_into().ok()?) as usize;
            let size = u64::from_le_bytes(elf_data[sh_offset + 32..sh_offset + 40].try_into().ok()?) as usize;

            match name {
                ".text" => text_section = Some((offset, size)),
                ".rela.text" => rela_text_section = Some((offset, size)),
                ".symtab" => symtab_section = Some((offset, size, sh_link as usize)),
                ".strtab" => strtab_offset = Some(offset),
                _ => {}
            }

            // SHT_SYMTAB = 2
            if sh_type == 2 && symtab_section.is_none() {
                symtab_section = Some((offset, size, sh_link as usize));
            }
        }
    }

    let (text_offset, text_size) = text_section?;
    if text_offset + text_size > elf_data.len() || text_size == 0 {
        return None;
    }

    let mut code = elf_data[text_offset..text_offset + text_size].to_vec();
    // Apply relocations if present
    if let (Some((rela_offset, rela_size)), Some((symtab_off, symtab_size, symtab_link))) =
        (rela_text_section, symtab_section)
    {
        // Get string table for symbol names
        let strtab_off = if let Some(off) = strtab_offset {
            off
        } else {
            // Get strtab from symtab's link field
            let link_sh_offset = e_shoff + symtab_link * e_shentsize;
            if link_sh_offset + e_shentsize <= elf_data.len() {
                u64::from_le_bytes(elf_data[link_sh_offset + 24..link_sh_offset + 32].try_into().ok()?) as usize
            } else {
                return Some(code);
            }
        };

        apply_elf_relocations(
            &mut code,
            elf_data,
            rela_offset,
            rela_size,
            symtab_off,
            symtab_size,
            strtab_off,
            text_offset,
        );

        // Handle GOT-relative relocations by appending inline GOT entries
        apply_got_relocations(&mut code, elf_data, rela_offset, rela_size, symtab_off, strtab_off);
    }

    Some(code)
}

/// Apply ELF relocations to extracted code.
fn apply_elf_relocations(
    code: &mut [u8],
    elf_data: &[u8],
    rela_offset: usize,
    rela_size: usize,
    symtab_off: usize,
    _symtab_size: usize,
    strtab_off: usize,
    _text_base: usize,
) {
    // ELF64 relocation entry size is 24 bytes
    const RELA_ENTRY_SIZE: usize = 24;
    // ELF64 symbol entry size is 24 bytes
    const SYM_ENTRY_SIZE: usize = 24;

    // R_X86_64_PLT32 = 4, R_X86_64_PC32 = 2
    const R_X86_64_PC32: u32 = 2;
    const R_X86_64_PLT32: u32 = 4;

    let num_relocs = rela_size / RELA_ENTRY_SIZE;

    for i in 0..num_relocs {
        let rela_entry = rela_offset + i * RELA_ENTRY_SIZE;
        if rela_entry + RELA_ENTRY_SIZE > elf_data.len() {
            continue;
        }

        let r_offset = u64::from_le_bytes(elf_data[rela_entry..rela_entry + 8].try_into().unwrap()) as usize;
        let r_info = u64::from_le_bytes(elf_data[rela_entry + 8..rela_entry + 16].try_into().unwrap());
        let r_addend = i64::from_le_bytes(elf_data[rela_entry + 16..rela_entry + 24].try_into().unwrap());

        let r_type = (r_info & 0xffffffff) as u32;
        let r_sym = (r_info >> 32) as usize;

        // Only handle PC32 and PLT32 relocations (function calls)
        if r_type != R_X86_64_PC32 && r_type != R_X86_64_PLT32 {
            continue;
        }

        // Get symbol info
        let sym_entry = symtab_off + r_sym * SYM_ENTRY_SIZE;
        if sym_entry + SYM_ENTRY_SIZE > elf_data.len() {
            continue;
        }

        let st_name = u32::from_le_bytes(elf_data[sym_entry..sym_entry + 4].try_into().unwrap()) as usize;

        // Get symbol name from string table
        let sym_name = get_elf_string(elf_data, strtab_off, st_name);

        // Resolve runtime symbol address
        if let Some(sym_addr) = resolve_runtime_symbol(&sym_name) {
            // Calculate patch location in the extracted code
            if r_offset < code.len() && r_offset + 4 <= code.len() {
                // For PC-relative relocations, we need to calculate the offset
                // from the instruction address to the target.
                // But since our code will be loaded at an unknown address,
                // we use an absolute call instead.
                //
                // The relocation is: S + A - P
                // where S = symbol address, A = addend, P = patch address
                //
                // Since we're extracting code to a different location,
                // we need to patch with absolute addresses. For PC32/PLT32,
                // we'll compute assuming the code starts at 0 and adjust.
                //
                // Actually, for AOT code that will be mmap'd, we should
                // leave relocations in SMF format for the loader to apply.
                // For now, we patch assuming the code will be at a fixed location.

                // The patch is relative to where the code will be executed.
                // We'll compute a direct offset from the code buffer base.
                let patch_offset_in_text = r_offset;

                // Calculate the relative offset
                // P = address of the 4-byte patch location
                // We want: S + A - P
                // where P is the runtime address of the patch location
                // Since we don't know where the code will be loaded,
                // we need to leave this as a relocation for the loader.

                // For immediate execution in same address space,
                // compute relative offset from the code buffer
                let code_ptr = code.as_ptr() as usize;
                let patch_addr = code_ptr + patch_offset_in_text;
                let value = ((sym_addr as i64) + r_addend - (patch_addr as i64)) as i32;

                code[r_offset..r_offset + 4].copy_from_slice(&value.to_le_bytes());
            }
        }
    }
}

/// Find the offset of a named symbol within the .text section of an ELF object.
/// Returns the symbol's value (offset within .text) or None if not found.
pub(crate) fn find_symbol_offset_in_object(object_code: &[u8], symbol_name: &str) -> Option<u64> {
    if object_code.len() < 64 || &object_code[0..4] != b"\x7fELF" {
        return None;
    }

    let e_shoff = u64::from_le_bytes(object_code[40..48].try_into().ok()?) as usize;
    let e_shentsize = u16::from_le_bytes(object_code[58..60].try_into().ok()?) as usize;
    let e_shnum = u16::from_le_bytes(object_code[60..62].try_into().ok()?) as usize;

    if e_shoff == 0 || e_shnum == 0 {
        return None;
    }

    // Find .symtab and .strtab sections
    let mut symtab: Option<(usize, usize, u32)> = None; // (offset, size, link)
    for i in 0..e_shnum {
        let sh_offset = e_shoff + i * e_shentsize;
        if sh_offset + e_shentsize > object_code.len() {
            continue;
        }
        let sh_type = u32::from_le_bytes(object_code[sh_offset + 4..sh_offset + 8].try_into().ok()?);
        // SHT_SYMTAB = 2
        if sh_type == 2 {
            let offset = u64::from_le_bytes(object_code[sh_offset + 24..sh_offset + 32].try_into().ok()?) as usize;
            let size = u64::from_le_bytes(object_code[sh_offset + 32..sh_offset + 40].try_into().ok()?) as usize;
            let link = u32::from_le_bytes(object_code[sh_offset + 40..sh_offset + 44].try_into().ok()?);
            symtab = Some((offset, size, link));
            break;
        }
    }

    let (symtab_off, symtab_size, strtab_idx) = symtab?;

    // Get strtab offset from linked section
    let strtab_sh_offset = e_shoff + strtab_idx as usize * e_shentsize;
    if strtab_sh_offset + e_shentsize > object_code.len() {
        return None;
    }
    let strtab_off = u64::from_le_bytes(
        object_code[strtab_sh_offset + 24..strtab_sh_offset + 32]
            .try_into()
            .ok()?,
    ) as usize;

    // Iterate symbols (ELF64 symbol entry = 24 bytes)
    const SYM_ENTRY_SIZE: usize = 24;
    let num_syms = symtab_size / SYM_ENTRY_SIZE;
    for i in 0..num_syms {
        let sym_entry = symtab_off + i * SYM_ENTRY_SIZE;
        if sym_entry + SYM_ENTRY_SIZE > object_code.len() {
            continue;
        }
        let st_name = u32::from_le_bytes(object_code[sym_entry..sym_entry + 4].try_into().ok()?) as usize;
        let st_value = u64::from_le_bytes(object_code[sym_entry + 8..sym_entry + 16].try_into().ok()?);
        let name = get_elf_string(object_code, strtab_off, st_name);
        if name == symbol_name {
            return Some(st_value);
        }
    }
    None
}

/// Handle GOT-relative relocations (R_X86_64_GOTPCREL = 9, GOTPCRELX = 41, REX_GOTPCRELX = 42).
/// Appends inline GOT entries to the code buffer and patches the displacement.
fn apply_got_relocations(
    code: &mut Vec<u8>,
    elf_data: &[u8],
    rela_offset: usize,
    rela_size: usize,
    symtab_off: usize,
    strtab_off: usize,
) {
    const RELA_ENTRY_SIZE: usize = 24;
    const SYM_ENTRY_SIZE: usize = 24;
    const R_X86_64_GOTPCREL: u32 = 9;
    const R_X86_64_GOTPCRELX: u32 = 41;
    const R_X86_64_REX_GOTPCRELX: u32 = 42;

    let num_relocs = rela_size / RELA_ENTRY_SIZE;
    // Track original code size (before GOT entries)
    let original_code_size = code.len();

    for i in 0..num_relocs {
        let rela_entry = rela_offset + i * RELA_ENTRY_SIZE;
        if rela_entry + RELA_ENTRY_SIZE > elf_data.len() {
            continue;
        }

        let r_offset = u64::from_le_bytes(elf_data[rela_entry..rela_entry + 8].try_into().unwrap()) as usize;
        let r_info = u64::from_le_bytes(elf_data[rela_entry + 8..rela_entry + 16].try_into().unwrap());
        let r_addend = i64::from_le_bytes(elf_data[rela_entry + 16..rela_entry + 24].try_into().unwrap());

        let r_type = (r_info & 0xffffffff) as u32;
        let r_sym = (r_info >> 32) as usize;

        if r_type != R_X86_64_GOTPCREL && r_type != R_X86_64_GOTPCRELX && r_type != R_X86_64_REX_GOTPCRELX {
            continue;
        }

        let sym_entry = symtab_off + r_sym * SYM_ENTRY_SIZE;
        if sym_entry + SYM_ENTRY_SIZE > elf_data.len() {
            continue;
        }
        let st_name = u32::from_le_bytes(elf_data[sym_entry..sym_entry + 4].try_into().unwrap()) as usize;
        let sym_name = get_elf_string(elf_data, strtab_off, st_name);

        if let Some(sym_addr) = resolve_runtime_symbol(&sym_name) {
            if r_offset < original_code_size && r_offset + 4 <= original_code_size {
                let got_offset = code.len();
                code.extend_from_slice(&(sym_addr as u64).to_le_bytes());
                // RIP-relative: disp = target - (r_offset + 4), where r_offset+4 is RIP after the disp field
                let disp = (got_offset as i64) - ((r_offset + 4) as i64);
                code[r_offset..r_offset + 4].copy_from_slice(&(disp as i32).to_le_bytes());
            }
        }
    }
}

/// Get a null-terminated string from ELF string table.
fn get_elf_string(elf_data: &[u8], strtab_off: usize, offset: usize) -> String {
    let start = strtab_off + offset;
    if start >= elf_data.len() {
        return String::new();
    }

    let end = elf_data[start..]
        .iter()
        .position(|&c| c == 0)
        .map(|p| start + p)
        .unwrap_or(elf_data.len());

    String::from_utf8_lossy(&elf_data[start..end]).into_owned()
}

/// Resolve a runtime symbol name to its address.
#[allow(clippy::fn_to_numeric_cast_any)]
fn resolve_runtime_symbol(name: &str) -> Option<usize> {
    // Map symbol names to function pointers
    let addr: usize = match name {
        // Array operations
        "rt_array_new" => simple_runtime::rt_array_new as *const () as usize,
        "rt_array_push" => simple_runtime::rt_array_push as *const () as usize,
        "rt_array_get" => simple_runtime::rt_array_get as *const () as usize,
        "rt_array_set" => simple_runtime::rt_array_set as *const () as usize,
        "rt_array_pop" => simple_runtime::rt_array_pop as *const () as usize,
        "rt_array_clear" => value::rt_array_clear as *const () as usize,

        // Tuple operations
        "rt_tuple_new" => simple_runtime::rt_tuple_new as *const () as usize,
        "rt_tuple_set" => simple_runtime::rt_tuple_set as *const () as usize,
        "rt_tuple_get" => simple_runtime::rt_tuple_get as *const () as usize,
        "rt_tuple_len" => simple_runtime::rt_tuple_len as *const () as usize,

        // Dict operations
        "rt_dict_new" => simple_runtime::rt_dict_new as *const () as usize,
        "rt_dict_set" => simple_runtime::rt_dict_set as *const () as usize,
        "rt_dict_get" => simple_runtime::rt_dict_get as *const () as usize,
        "rt_dict_len" => simple_runtime::rt_dict_len as *const () as usize,
        "rt_dict_clear" => value::rt_dict_clear as *const () as usize,
        "rt_dict_keys" => value::rt_dict_keys as *const () as usize,
        "rt_dict_values" => value::rt_dict_values as *const () as usize,

        // Index/slice operations
        "rt_index_get" => simple_runtime::rt_index_get as *const () as usize,
        "rt_index_set" => simple_runtime::rt_index_set as *const () as usize,
        "rt_slice" => simple_runtime::rt_slice as *const () as usize,
        "rt_contains" => value::rt_contains as *const () as usize,

        // String operations
        "rt_string_new" => simple_runtime::rt_string_new as *const () as usize,
        "rt_string_concat" => simple_runtime::rt_string_concat as *const () as usize,
        "rt_cstring_to_text" => simple_runtime::rt_cstring_to_text as *const () as usize,

        // Value creation/conversion
        "rt_value_int" => simple_runtime::rt_value_int as *const () as usize,
        "rt_value_float" => simple_runtime::rt_value_float as *const () as usize,
        "rt_value_bool" => simple_runtime::rt_value_bool as *const () as usize,
        "rt_value_nil" => simple_runtime::rt_value_nil as *const () as usize,
        "rt_value_as_int" => simple_runtime::rt_value_as_int as *const () as usize,

        // Object operations
        "rt_object_new" => simple_runtime::rt_object_new as *const () as usize,
        "rt_object_field_get" => simple_runtime::rt_object_field_get as *const () as usize,
        "rt_object_field_set" => simple_runtime::rt_object_field_set as *const () as usize,

        // Closure operations
        "rt_closure_new" => simple_runtime::rt_closure_new as *const () as usize,
        "rt_closure_set_capture" => simple_runtime::rt_closure_set_capture as *const () as usize,
        "rt_closure_get_capture" => simple_runtime::rt_closure_get_capture as *const () as usize,
        "rt_closure_func_ptr" => simple_runtime::rt_closure_func_ptr as *const () as usize,

        // Enum operations
        "rt_enum_new" => simple_runtime::rt_enum_new as *const () as usize,
        "rt_enum_discriminant" => simple_runtime::rt_enum_discriminant as *const () as usize,
        "rt_enum_payload" => simple_runtime::rt_enum_payload as *const () as usize,

        // Raw memory allocation
        "rt_alloc" => simple_runtime::rt_alloc as *const () as usize,
        "rt_free" => simple_runtime::rt_free as *const () as usize,
        "rt_ptr_to_value" => simple_runtime::rt_ptr_to_value as *const () as usize,
        "rt_value_to_ptr" => simple_runtime::rt_value_to_ptr as *const () as usize,

        // Async/concurrency operations
        "rt_wait" => simple_runtime::rt_wait as *const () as usize,
        "rt_future_new" => simple_runtime::rt_future_new as *const () as usize,
        "rt_future_await" => simple_runtime::rt_future_await as *const () as usize,
        "rt_actor_spawn" => simple_runtime::rt_actor_spawn as *const () as usize,
        "rt_actor_send" => simple_runtime::rt_actor_send as *const () as usize,
        "rt_actor_recv" => simple_runtime::rt_actor_recv as *const () as usize,

        // Generator operations
        "rt_generator_new" => simple_runtime::rt_generator_new as *const () as usize,
        "rt_generator_next" => simple_runtime::rt_generator_next as *const () as usize,
        "rt_generator_get_state" => simple_runtime::rt_generator_get_state as *const () as usize,
        "rt_generator_set_state" => simple_runtime::rt_generator_set_state as *const () as usize,
        "rt_generator_store_slot" => simple_runtime::rt_generator_store_slot as *const () as usize,
        "rt_generator_load_slot" => simple_runtime::rt_generator_load_slot as *const () as usize,
        "rt_generator_get_ctx" => simple_runtime::rt_generator_get_ctx as *const () as usize,
        "rt_generator_mark_done" => simple_runtime::rt_generator_mark_done as *const () as usize,

        // Interpreter bridge FFI
        "rt_interp_call" => value::rt_interp_call as *const () as usize,
        "rt_interp_eval" => value::rt_interp_eval as *const () as usize,

        // Comparison/equality operations
        "rt_value_compare" => value::rt_value_compare as *const () as usize,
        "rt_value_eq" => value::rt_value_eq as *const () as usize,

        // Error handling
        "rt_function_not_found" => value::rt_function_not_found as *const () as usize,
        "rt_method_not_found" => value::rt_method_not_found as *const () as usize,

        // I/O operations
        "rt_print_str" => value::rt_print_str as *const () as usize,
        "rt_println_str" => value::rt_println_str as *const () as usize,
        "rt_eprint_str" => value::rt_eprint_str as *const () as usize,
        "rt_eprintln_str" => value::rt_eprintln_str as *const () as usize,
        "rt_print_value" => value::rt_print_value as *const () as usize,
        "rt_println_value" => value::rt_println_value as *const () as usize,
        "rt_eprint_value" => value::rt_eprint_value as *const () as usize,
        "rt_eprintln_value" => value::rt_eprintln_value as *const () as usize,
        "rt_capture_stdout_start" => value::rt_capture_stdout_start as *const () as usize,
        "rt_capture_stderr_start" => value::rt_capture_stderr_start as *const () as usize,

        // Doctest I/O operations (file discovery)
        "doctest_read_file" => simple_runtime::doctest_read_file as *const () as usize,
        "doctest_path_exists" => simple_runtime::doctest_path_exists as *const () as usize,
        "doctest_is_file" => simple_runtime::doctest_is_file as *const () as usize,
        "doctest_is_dir" => simple_runtime::doctest_is_dir as *const () as usize,
        "doctest_walk_directory" => simple_runtime::doctest_walk_directory as *const () as usize,
        "doctest_path_has_extension" => simple_runtime::doctest_path_has_extension as *const () as usize,
        "doctest_path_contains" => simple_runtime::doctest_path_contains as *const () as usize,

        // Cranelift FFI operations (for self-hosting compiler)
        "rt_cranelift_module_new" => crate::codegen::cranelift_ffi::rt_cranelift_module_new as *const () as usize,
        "rt_cranelift_new_module" => crate::codegen::cranelift_ffi::rt_cranelift_new_module as *const () as usize,
        "rt_cranelift_finalize_module" => {
            crate::codegen::cranelift_ffi::rt_cranelift_finalize_module as *const () as usize
        }
        "rt_cranelift_free_module" => crate::codegen::cranelift_ffi::rt_cranelift_free_module as *const () as usize,
        "rt_cranelift_new_signature" => crate::codegen::cranelift_ffi::rt_cranelift_new_signature as *const () as usize,
        "rt_cranelift_sig_add_param" => crate::codegen::cranelift_ffi::rt_cranelift_sig_add_param as *const () as usize,
        "rt_cranelift_sig_set_return" => {
            crate::codegen::cranelift_ffi::rt_cranelift_sig_set_return as *const () as usize
        }
        "rt_cranelift_begin_function" => {
            crate::codegen::cranelift_ffi::rt_cranelift_begin_function as *const () as usize
        }
        "rt_cranelift_end_function" => crate::codegen::cranelift_ffi::rt_cranelift_end_function as *const () as usize,
        "rt_cranelift_define_function" => {
            crate::codegen::cranelift_ffi::rt_cranelift_define_function as *const () as usize
        }
        "rt_cranelift_create_block" => crate::codegen::cranelift_ffi::rt_cranelift_create_block as *const () as usize,
        "rt_cranelift_switch_to_block" => {
            crate::codegen::cranelift_ffi::rt_cranelift_switch_to_block as *const () as usize
        }
        "rt_cranelift_seal_block" => crate::codegen::cranelift_ffi::rt_cranelift_seal_block as *const () as usize,
        "rt_cranelift_seal_all_blocks" => {
            crate::codegen::cranelift_ffi::rt_cranelift_seal_all_blocks as *const () as usize
        }
        "rt_cranelift_iconst" => crate::codegen::cranelift_ffi::rt_cranelift_iconst as *const () as usize,
        "rt_cranelift_return" => crate::codegen::cranelift_ffi::rt_cranelift_return as *const () as usize,
        "rt_cranelift_return_void" => crate::codegen::cranelift_ffi::rt_cranelift_return_void as *const () as usize,
        "rt_cranelift_emit_object" => crate::codegen::cranelift_ffi::rt_cranelift_emit_object as *const () as usize,

        _ => return None,
    };

    Some(addr)
}
