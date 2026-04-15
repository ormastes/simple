//! MIR name mangling for the LLVM backend.
//!
//! The Cranelift backend does mangling at codegen time via `module_prefix`, `import_map`, etc.
//! The LLVM backend operates on MIR names directly, so we mangle MIR before passing it.

use super::imports::{resolve_name_variants, resolve_by_suffix, suffix_of};

/// Apply name mangling to a MIR module for the LLVM backend.
pub(crate) fn mangle_mir(
    mir: &mut crate::mir::MirModule,
    prefix: &str,
    is_entry: bool,
    import_map: &std::collections::HashMap<String, String>,
    ambiguous_names: &std::collections::HashSet<String>,
    use_map: &std::collections::HashMap<String, String>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) -> usize {
    use crate::mir::MirInst;

    let mut unresolved_count: usize = 0;

    // Extern fn declarations from this module must never be mangled.
    let extern_fns = mir.extern_fn_names.clone();

    // Names that should never be mangled (runtime functions, builtins).
    let is_runtime_or_builtin = |name: &str| -> bool { is_runtime_or_builtin_name(name, &extern_fns) };

    // Build set of locally-defined function names.
    let local_fn_names: std::collections::HashSet<String> = mir
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.name.clone())
        .collect();

    // Build set of all known fully-qualified imported names.
    let imported_qualified: std::collections::HashSet<String> = {
        let mut set = std::collections::HashSet::new();
        for v in import_map.values().chain(use_map.values()) {
            set.insert(v.clone());
            if v.contains('.') {
                set.insert(v.replace('.', "_dot_"));
            }
            if v.contains("_dot_") {
                set.insert(v.replace("_dot_", "."));
            }
        }
        set
    };

    // Build a mapping from raw name -> mangled name for local functions.
    let mut local_mangled: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for func in &mir.functions {
        let has_body = !func.blocks.is_empty();
        if !has_body {
            continue;
        }
        if is_runtime_or_builtin(&func.name) {
            continue;
        }
        if imported_qualified.contains(&func.name) {
            continue;
        }
        let mangled = if func.name == "main" {
            if is_entry {
                "spl_main".to_string()
            } else {
                format!("{}__{}", prefix, func.name)
            }
        } else {
            format!("{}__{}", prefix, func.name)
        };
        local_mangled.insert(func.name.clone(), mangled);
    }

    // Build local suffix index from this module's known names.
    let mut local_suffix_index: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    for resolved in local_mangled
        .values()
        .chain(use_map.values())
        .chain(import_map.values())
    {
        if let Some(suffix) = suffix_of(resolved) {
            local_suffix_index
                .entry(suffix.to_string())
                .or_default()
                .push(resolved.clone());
            if let Some(dot_pos) = suffix.rfind('.') {
                let sub_suffix = &suffix[dot_pos + 1..];
                if !sub_suffix.is_empty() {
                    local_suffix_index
                        .entry(sub_suffix.to_string())
                        .or_default()
                        .push(resolved.clone());
                }
            }
        }
    }

    // Build a mapping from raw name -> mangled name for local globals.
    let mut local_global_mangled: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for (name, _ty, _is_mut) in &mir.globals {
        if mir.local_globals.contains(name) && !is_runtime_or_builtin(name) {
            local_global_mangled.insert(name.clone(), format!("{}__{}", prefix, name));
        }
    }

    // Phase 1: Rename function definitions
    for func in &mut mir.functions {
        if let Some(mangled) = local_mangled.get(&func.name) {
            func.name = mangled.clone();
        }
    }

    // Phase 2: Rename globals in mir.globals, global_init_values, local_globals
    let mut new_globals = Vec::new();
    for (name, ty, is_mut) in &mir.globals {
        if let Some(mangled) = local_global_mangled.get(name) {
            new_globals.push((mangled.clone(), *ty, *is_mut));
        } else {
            new_globals.push((name.clone(), *ty, *is_mut));
        }
    }
    mir.globals = new_globals;

    let old_init = std::mem::take(&mut mir.global_init_values);
    for (name, val) in old_init {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.global_init_values.insert(mangled.clone(), val);
        } else {
            mir.global_init_values.insert(name, val);
        }
    }

    let old_init_strings = std::mem::take(&mut mir.global_init_strings);
    for (name, val) in old_init_strings {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.global_init_strings.insert(mangled.clone(), val);
        } else {
            mir.global_init_strings.insert(name, val);
        }
    }

    let old_local = std::mem::take(&mut mir.local_globals);
    for name in old_local {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.local_globals.insert(mangled.clone());
        } else {
            mir.local_globals.insert(name);
        }
    }

    // Build a set of all known mangled names.
    let known_mangled: std::collections::HashSet<String> = {
        let mut set: std::collections::HashSet<String> = import_map
            .values()
            .chain(use_map.values())
            .chain(local_mangled.values())
            .cloned()
            .collect();
        let extras: Vec<String> = set
            .iter()
            .filter_map(|v| {
                if v.contains('.') {
                    Some(v.replace('.', "_dot_"))
                } else if v.contains("_dot_") {
                    Some(v.replace("_dot_", "."))
                } else {
                    None
                }
            })
            .collect();
        set.extend(extras);
        set
    };

    // Phase 3: Rename call targets and global references in instructions.
    for func in &mut mir.functions {
        for block in &mut func.blocks {
            for inst in &mut block.instructions {
                match inst {
                    MirInst::Call { target, .. } => {
                        let name = target.name().to_string();
                        if is_runtime_or_builtin(&name) {
                            continue;
                        }
                        if known_mangled.contains(name.as_str()) {
                            continue;
                        }
                        if name.contains("_dot_") {
                            let converted = name.replace("_dot_", ".");
                            if known_mangled.contains(converted.as_str()) {
                                *target = target.with_name(converted);
                                continue;
                            }
                        }
                        if let Some(mangled) = local_mangled.get(&name) {
                            *target = target.with_name(mangled.clone());
                        } else if let Some(resolved) = use_map.get(&name) {
                            *target = target.with_name(resolved.clone());
                        } else {
                            let method_dot = format!(".{}", name);
                            let mut use_resolved = None;
                            for (raw, mangled) in use_map.iter() {
                                if raw.ends_with(&method_dot) && raw.len() > name.len() + 1 {
                                    use_resolved = Some(mangled.clone());
                                    break;
                                }
                            }
                            if use_resolved.is_none() {
                                for (raw, mangled) in import_map.iter() {
                                    if raw.ends_with(&method_dot) && raw.len() > name.len() + 1 {
                                        let type_part = &raw[..raw.len() - method_dot.len()];
                                        if use_map.contains_key(type_part) {
                                            use_resolved = Some(mangled.clone());
                                            break;
                                        }
                                    }
                                }
                            }
                            if let Some(resolved) = use_resolved {
                                *target = target.with_name(resolved);
                            } else if let Some(resolved) = import_map.get(&name) {
                                *target = target.with_name(resolved.clone());
                            }
                        }
                        let name = target.name().to_string();
                        if !known_mangled.contains(name.as_str()) && !is_runtime_or_builtin(&name) {
                            resolve_call_target(
                                target,
                                &name,
                                use_map,
                                import_map,
                                &local_suffix_index,
                                suffix_index,
                                &func.name,
                                prefix,
                                &mut unresolved_count,
                            );
                        }
                    }
                    MirInst::InterpCall { func_name, .. } => {
                        if is_runtime_or_builtin(func_name) || known_mangled.contains(func_name.as_str()) {
                            continue;
                        }
                        if let Some(resolved) = resolve_name(
                            func_name,
                            &local_mangled,
                            use_map,
                            import_map,
                            &local_suffix_index,
                            suffix_index,
                        ) {
                            *func_name = resolved;
                        }
                    }
                    MirInst::GlobalLoad { global_name, .. } | MirInst::GlobalStore { global_name, .. } => {
                        if is_runtime_or_builtin(global_name) || known_mangled.contains(global_name.as_str()) {
                            continue;
                        }
                        if let Some(resolved) = resolve_name(
                            global_name,
                            &local_global_mangled,
                            use_map,
                            import_map,
                            &local_suffix_index,
                            suffix_index,
                        ) {
                            *global_name = resolved;
                        }
                    }
                    MirInst::MethodCallStatic { func_name, .. } => {
                        if is_runtime_or_builtin(func_name) || known_mangled.contains(func_name.as_str()) {
                            continue;
                        }
                        if func_name.contains("_dot_") {
                            let converted = func_name.replace("_dot_", ".");
                            if known_mangled.contains(converted.as_str()) {
                                *func_name = converted;
                                continue;
                            }
                            if let Some(resolved) = use_map
                                .get(converted.as_str())
                                .or_else(|| import_map.get(converted.as_str()))
                            {
                                *func_name = resolved.clone();
                                continue;
                            }
                        }
                        if let Some(mangled) = local_mangled.get(func_name.as_str()) {
                            *func_name = mangled.clone();
                        } else if let Some(resolved) = use_map.get(func_name.as_str()) {
                            *func_name = resolved.clone();
                        } else {
                            let method_part = func_name.as_str();
                            let mut use_resolved = None;
                            for (raw, mangled) in use_map.iter() {
                                if raw.ends_with(&format!(".{}", method_part)) && raw.len() > method_part.len() + 1 {
                                    use_resolved = Some(mangled.clone());
                                    break;
                                }
                            }
                            if let Some(resolved) = use_resolved {
                                *func_name = resolved;
                            } else if let Some(resolved) = import_map.get(func_name.as_str()) {
                                *func_name = resolved.clone();
                            }
                        }
                        if !known_mangled.contains(func_name.as_str()) && !is_runtime_or_builtin(func_name) {
                            resolve_method_call_static(
                                func_name,
                                use_map,
                                import_map,
                                &local_suffix_index,
                                suffix_index,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    unresolved_count
}

/// Resolve a name by checking local_map → use_map → import_map → variant resolution → suffix resolution.
///
/// This is the common resolution chain used by InterpCall, GlobalLoad/GlobalStore, and other
/// instruction types that need to resolve a raw name to its mangled/qualified form.
fn resolve_name(
    name: &str,
    local_map: &std::collections::HashMap<String, String>,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    local_suffix_index: &std::collections::HashMap<String, Vec<String>>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) -> Option<String> {
    if let Some(mangled) = local_map.get(name) {
        Some(mangled.clone())
    } else if let Some(resolved) = use_map.get(name) {
        Some(resolved.clone())
    } else if let Some(resolved) = import_map.get(name) {
        Some(resolved.clone())
    } else if let Some(resolved) = resolve_name_variants(name, use_map, import_map) {
        Some(resolved)
    } else {
        resolve_by_suffix(name, local_suffix_index).or_else(|| resolve_by_suffix(name, suffix_index))
    }
}

/// Resolve a Call target that is still unresolved after local/use_map/import_map lookup.
fn resolve_call_target(
    target: &mut crate::mir::CallTarget,
    name: &str,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    local_suffix_index: &std::collections::HashMap<String, Vec<String>>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
    func_name: &str,
    prefix: &str,
    unresolved_count: &mut usize,
) {
    if let Some(resolved) = resolve_name_variants(name, use_map, import_map) {
        *target = target.with_name(resolved);
    } else if name.contains('.') {
        let method = name.rsplit('.').next().unwrap_or(name);
        let type_part = name.split('.').next().unwrap_or("");
        let candidates = local_suffix_index
            .get(name)
            .or_else(|| suffix_index.get(name))
            .or_else(|| local_suffix_index.get(method))
            .or_else(|| suffix_index.get(method));
        if let Some(candidates) = candidates {
            let best = candidates
                .iter()
                .find(|c| c.to_lowercase().contains(&type_part.to_lowercase()))
                .or_else(|| {
                    if candidates.len() == 1 {
                        candidates.first()
                    } else {
                        None
                    }
                });
            if let Some(b) = best {
                *target = target.with_name(b.clone());
            } else if let Some(resolved) =
                resolve_by_suffix(name, local_suffix_index).or_else(|| resolve_by_suffix(name, suffix_index))
            {
                *target = target.with_name(resolved);
            } else {
                *unresolved_count += 1;
                eprintln!(
                    "warning: unresolved call `{}` in function `{}` (module: {})",
                    name, func_name, prefix
                );
            }
        } else if let Some(resolved) =
            resolve_by_suffix(name, local_suffix_index).or_else(|| resolve_by_suffix(name, suffix_index))
        {
            *target = target.with_name(resolved);
        } else {
            *unresolved_count += 1;
            eprintln!(
                "warning: unresolved call `{}` in function `{}` (module: {})",
                name, func_name, prefix
            );
        }
    } else if let Some(resolved) =
        resolve_by_suffix(name, local_suffix_index).or_else(|| resolve_by_suffix(name, suffix_index))
    {
        *target = target.with_name(resolved);
    } else {
        *unresolved_count += 1;
        eprintln!(
            "warning: unresolved call `{}` in function `{}` (module: {})",
            name, func_name, prefix
        );
    }
}

/// Resolve a MethodCallStatic target that is still unresolved.
fn resolve_method_call_static(
    func_name: &mut String,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    local_suffix_index: &std::collections::HashMap<String, Vec<String>>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) {
    if let Some(resolved) = resolve_name_variants(func_name, use_map, import_map) {
        *func_name = resolved;
    } else {
        let method = func_name.rsplit('.').next().unwrap_or(func_name);
        let type_part = func_name.split('.').next().unwrap_or("");
        let has_type_qualifier = func_name.contains('.');
        let type_part_lower = type_part.to_lowercase();
        let candidates = local_suffix_index.get(method).or_else(|| suffix_index.get(method));
        if let Some(candidates) = candidates {
            let best = if has_type_qualifier {
                candidates.iter().find(|c| c.to_lowercase().contains(&type_part_lower))
            } else {
                let mut use_match: Option<&String> = None;
                for (raw, mangled) in use_map.iter() {
                    if raw.ends_with(&format!(".{}", method)) {
                        if let Some(c) = candidates.iter().find(|c| *c == mangled) {
                            use_match = Some(c);
                            break;
                        }
                    }
                }
                if use_match.is_none() {
                    for (raw, mangled) in import_map.iter() {
                        if raw.ends_with(&format!(".{}", method)) && raw != method {
                            if let Some(c) = candidates.iter().find(|c| *c == mangled) {
                                let raw_type = raw.split('.').next().unwrap_or("");
                                if use_map.contains_key(raw_type) {
                                    use_match = Some(c);
                                    break;
                                }
                            }
                        }
                    }
                }
                use_match
            };
            let best = best.or_else(|| {
                if candidates.len() == 1 {
                    candidates.first()
                } else {
                    None
                }
            });
            if let Some(b) = best {
                *func_name = b.clone();
            }
        } else if let Some(resolved) =
            resolve_by_suffix(func_name, local_suffix_index).or_else(|| resolve_by_suffix(func_name, suffix_index))
        {
            *func_name = resolved;
        }
    }
}

/// Check if a name is a runtime/builtin that should never be mangled.
fn is_runtime_or_builtin_name(name: &str, extern_fns: &std::collections::HashSet<String>) -> bool {
    extern_fns.contains(name)
        || name.starts_with("rt_")
        || name.starts_with("__simple_")
        || name.starts_with("spl_")
        || name.starts_with("__get_global_")
        || name.starts_with("__set_global_")
        || name.starts_with("bit_")
        || name.starts_with("bitwise_")
        || name.starts_with("ffi_")
        || name.starts_with("rc_box_")
        || name.starts_with("arc_box_")
        || (name.contains('.') && {
            let prefix = name.split('.').next().unwrap_or("");
            !prefix.is_empty()
                && prefix
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
        })
        || name.ends_with("_contains_key")
        || matches!(
            name,
            "print"
                | "println"
                | "eprint"
                | "eprintln"
                | "print_raw"
                | "eprint_raw"
                | "dprint"
                | "Ok"
                | "Err"
                | "Some"
                | "None"
                | "len"
                | "push"
                | "pop"
                | "get"
                | "clear"
                | "contains"
                | "starts_with"
                | "ends_with"
                | "concat"
                | "char_at"
                | "at"
                | "join"
                | "trim"
                | "split"
                | "replace"
                | "to_upper"
                | "upper"
                | "to_lower"
                | "lower"
                | "to_int"
                | "to_i64"
                | "parse_int"
                | "to_float"
                | "to_f64"
                | "parse_float"
                | "parse_f64"
                | "parse_f64_safe"
                | "to_string"
                | "str"
                | "slice"
                | "substring"
                | "keys"
                | "values"
                | "filter"
                | "sort"
                | "reverse"
                | "first"
                | "last"
                | "find"
                | "any"
                | "all"
                | "map"
                | "each"
                | "reduce"
                | "fold"
                | "asm"
                | "unsafe"
                | "assert"
                | "Dict"
                | "traverse"
                | "func"
                | "line_trim"
                | "malloc"
                | "free"
                | "calloc"
                | "realloc"
                | "memset"
                | "memcpy"
                | "memmove"
                | "madvise"
                | "mmap"
                | "mmap_file"
                | "munmap"
                | "readln"
                | "input"
                | "input_line"
                | "input_chars"
                | "env_var"
                | "env_args"
                | "env_clone"
                | "temp_dir"
                | "file_mtime"
                | "file_size_for_mmap"
                | "fs_read_text"
                | "fs_write_text"
                | "fs_has_file"
                | "fs_has_file_or_dir"
                | "dir_list_recursive"
                | "__traits"
                | "Error"
                | "VReg"
                | "Generic"
                | "trim_end"
                | "trim_start"
                | "string_from_byte"
                | "string_from_char_code"
                | "from_char_code"
                | "i64_max"
                | "text_index_of"
                | "current_rss_kb_main"
                | "array_length"
                | "array_new"
                | "mmap_read_string"
                | "mmap_read_bytes"
                | "interpret_ast"
                | "execute_compiled"
                | "handler"
                | "highlighter"
                | "completer"
                | "validator"
                | "AtomicI64"
                | "CircuitBreakerConfig"
                | "RateLimitConfig"
                | "ResourceLimits"
                | "TimeoutConfig"
                | "run_benchmarks"
                | "run_arch_check"
                | "validate_databases"
                | "test_user_service"
                | "register_builtin_blocks"
                | "sql_keywords"
                | "path_pop"
                | "new_text_lines"
                | "old_text_lines"
                | "new_to_clone"
                | "parent_clone"
                | "cycle_path_clone"
                | "upx_ensure_available"
                | "upx_get_path"
                | "self_extract_create"
                | "self_extract_is_compressed"
                | "JsonBlockDef"
                | "MathBlockDef"
                | "ShellBlockDef"
                | "SqlBlockDef"
                | "RegexBlockDef"
                | "MarkdownBlockDef"
                | "NogradBlockDef"
                | "LossBlockDef"
                | "make_cuda_port"
                | "make_vulkan_port"
                | "lexer_create_internal"
                | "mlr_lower_module"
                | "hir_expr_type"
                | "hir_pool_get"
                | "json_to_const"
                | "linkercompilationcontext_from_objects"
                | "search_recursive"
                | "find_decreases"
                | "find_scope_ancestor"
                | "calls_itself"
                | "hover_fn"
                | "daemon_send_request"
                | "parse_shell_commands"
                | "count_leading_chars"
                | "count_trailing_chars"
                | "line_trim_start"
                | "trimmed_is_empty"
                | "transcriber_is_empty"
                | "trait__is_none"
                | "type__size_bytes"
                | "next_lexeme_value_chars"
                | "matching_sort_by"
                | "mp_segments"
        )
}
