//! MIR name mangling for the LLVM backend.
//!
//! The Cranelift backend does mangling at codegen time via `module_prefix`, `import_map`, etc.
//! The LLVM backend operates on MIR names directly, so we mangle MIR before passing it.

use super::imports::{resolve_name_variants, resolve_by_suffix, suffix_of};

fn dotted_enum_runtime_name(mangled: &str) -> String {
    mangled.replace("_dot_", ".").replace("__", ".")
}

fn qualify_enum_pattern(
    pattern: &mut crate::mir::MirPattern,
    qualify: &impl Fn(&str) -> Result<String, String>,
) -> Result<(), String> {
    use crate::mir::MirPattern;
    match pattern {
        MirPattern::Variant { enum_name, payload, .. } => {
            *enum_name = qualify(enum_name)?;
            if let Some(payload) = payload {
                qualify_enum_pattern(payload, qualify)?;
            }
        }
        MirPattern::Tuple(items) | MirPattern::Or(items) => {
            for item in items {
                qualify_enum_pattern(item, qualify)?;
            }
        }
        MirPattern::Struct { fields, .. } => {
            for (_, field) in fields {
                qualify_enum_pattern(field, qualify)?;
            }
        }
        MirPattern::Guard { pattern, .. } => qualify_enum_pattern(pattern, qualify)?,
        MirPattern::Union { inner: Some(inner), .. } => qualify_enum_pattern(inner, qualify)?,
        _ => {}
    }
    Ok(())
}

/// Replace bare enum owners in constructor and pattern MIR with stable,
/// declaring-module-qualified runtime identities before either native backend.
pub(crate) fn qualify_enum_runtime_names(
    mir: &mut crate::mir::MirModule,
    runtime_module_name: &str,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    runtime_names: &std::collections::HashMap<String, String>,
) -> Result<(), String> {
    use crate::hir::HirType;
    use crate::mir::MirInst;

    let local_enums: std::collections::HashSet<String> = mir
        .local_globals
        .iter()
        .filter(|name| {
            mir.type_registry
                .lookup(name)
                .and_then(|id| mir.type_registry.get(id))
                .is_some_and(|ty| matches!(ty, HirType::Enum { .. }))
        })
        .cloned()
        .collect();
    let known_enums: std::collections::HashSet<String> = mir
        .type_registry
        .iter()
        .filter_map(|(_, ty)| match ty {
            HirType::Enum { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let known_runtime_names: std::collections::HashSet<&str> = runtime_names.values().map(String::as_str).collect();
    let local_runtime_name = |name: &str| {
        if runtime_module_name.is_empty() {
            name.to_string()
        } else {
            format!("{runtime_module_name}.{name}")
        }
    };

    let mut names = runtime_names.values().cloned().collect::<Vec<_>>();
    names.extend(local_enums.iter().map(|name| local_runtime_name(name)));
    names.sort();
    names.dedup();
    let mut ids = std::collections::HashMap::new();
    for name in names {
        let id = crate::codegen::shared::enum_runtime_type_id(&name);
        if let Some(existing) = ids.insert(id, name.clone()) {
            return Err(format!("enum runtime ID collision: '{existing}' and '{name}'"));
        }
    }

    let qualify = |name: &str| -> Result<String, String> {
        if known_runtime_names.contains(name) {
            return Ok(name.to_string());
        }
        let resolved = if local_enums.contains(name) {
            return Ok(local_runtime_name(name));
        } else {
            use_map.get(name).or_else(|| import_map.get(name)).cloned()
        };
        if let Some(resolved) = resolved {
            return Ok(runtime_names
                .get(&resolved)
                .cloned()
                .unwrap_or_else(|| dotted_enum_runtime_name(&resolved)));
        }
        // A module may construct a uniquely declared enum through a facade or
        // legacy import path that did not survive use-map resolution. The
        // global enum sidecar still has the authoritative mangled owner. Use
        // that identity only when the bare enum suffix is globally unique;
        // never guess between duplicate enum names.
        let mangled_suffix = format!("__{name}");
        let mut suffix_matches = runtime_names
            .iter()
            .filter(|(mangled, _)| *mangled == name || mangled.ends_with(&mangled_suffix))
            .map(|(_, runtime_name)| runtime_name.as_str());
        if let Some(unique) = suffix_matches.next() {
            if suffix_matches.next().is_none() {
                return Ok(unique.to_string());
            }
        }
        if matches!(name, "Result" | "Option") {
            return Ok(name.to_string());
        }
        if name.contains("__") || name.contains('.') {
            return Ok(dotted_enum_runtime_name(name));
        }
        // Some runtime/library enum owners are supplied outside the selected
        // source closure (for example ByteOrder), so no declaring-module
        // sidecar exists in this build. After exhausting every authoritative
        // local/import/global route, retain the bare owner as the stable
        // external runtime identity. Collisions among declarations that are
        // present in the build are still rejected while constructing the
        // global enum sidecar above.
        Ok(name.to_string())
    };

    for func in &mut mir.functions {
        for block in &mut func.blocks {
            for inst in &mut block.instructions {
                match inst {
                    MirInst::EnumUnit { enum_name, .. } | MirInst::EnumWith { enum_name, .. } => {
                        *enum_name = qualify(enum_name)?;
                    }
                    MirInst::PatternTest { pattern, .. } => qualify_enum_pattern(pattern, &qualify)?,
                    MirInst::Call { target, .. } => {
                        let name = target.name();
                        if let Some((owner, variant)) = name.rsplit_once("::") {
                            let resolved_owner = use_map.get(owner).or_else(|| import_map.get(owner));
                            let is_custom_enum = known_enums.contains(owner)
                                || local_enums.contains(owner)
                                || resolved_owner.is_some_and(|resolved| runtime_names.contains_key(resolved));
                            if is_custom_enum {
                                *target = target.with_name(format!("{}::{variant}", qualify(owner)?));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

/// The Optional/Result helper methods, which codegen lowers as builtins.
///
/// A BARE call target with one of these names must never be suffix-rebound to a
/// user method of the same name. macOS Stage 2 linker blocker, 2026-09-13:
/// `mold_path.unwrap()` on a `text?` (`mold.spl:704`) lowers to a bare `unwrap`
/// call target; the bare `.method` scans below then bound it to the ONLY
/// `.unwrap` entry reachable from the import maps,
/// `lib__nogc_async_mut__async__poll__Poll.unwrap`, which returns 0 for a text
/// receiver. `find_linker_path` therefore returned `Ok(0)`,
/// `darwin_resolve_link_tool(0)` failed `file_exists`, and the hello-world link
/// died as `Linking failed: no error payload from link_to_native`.
///
/// `resolve_call_target` and `resolve_method_call_static` already refuse this
/// (their guards citing the `FailSafeResult.unwrap` RV64 leak), but those run
/// only when the earlier scans left the name unresolved — once a scan rebinds,
/// `known_mangled` holds the new name and the guarded resolver is skipped
/// entirely. The guard has to be here as well, not only there.
///
/// Leaving the name bare routes it through codegen's `bare_rt_redirect` table,
/// which is the correct lowering for every receiver representation.
fn is_enum_helper_method(name: &str) -> bool {
    matches!(
        name,
        "unwrap" | "unwrap_or" | "unwrap_err" | "is_some" | "is_none" | "is_ok" | "is_err"
    )
}

/// Owner-segment match for an enum-helper rebind.
///
/// A mangled candidate is `<module__path>__<Owner>.<method>`; the owner is the
/// segment between the last `__` and the `.`. For the enum helpers the ONLY
/// safe rebind is one where the receiver qualifier names that owner exactly.
///
/// The `contains(type_part)` heuristic the generic arms use is actively unsafe
/// here: lowercased, the single Stage 2 candidate
/// `lib__nogc_async_mut__async__poll__Poll.unwrap` contains the letters of most
/// short type names, so a generic parameter (`T`, `R`, `U`) or a type called
/// `Mut` / `Sync` / `Async` / `Lib` / `Wrap` substring-matches it and gets its
/// `.unwrap()` bound to an unrelated type's method, which returns 0 for a
/// non-`Poll` receiver (2026-09-13, 208 residual sites across 109 functions).
fn enum_helper_owner_matches(candidate: &str, type_part: &str) -> bool {
    let Some((owner_path, _method)) = candidate.rsplit_once('.') else {
        return false;
    };
    let owner = owner_path.rsplit("__").next().unwrap_or(owner_path);
    owner.eq_ignore_ascii_case(type_part)
}

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

    // Build a mapping from raw name -> mangled name for local functions.
    let mut local_mangled: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for func in &mir.functions {
        let has_body = !func.blocks.is_empty();
        if !has_body {
            continue;
        }
        // `@global` (design A.2): the symbol keeps its unmangled Simple name
        // so `.S`-era labels (`_start`, `vector_table`) survive to the linker.
        let keeps_abi_name = func.attributes.iter().any(|attr| attr == "export" || attr == "global")
            || extern_fns.contains(&func.name)
            || func.name.starts_with("__simple_")
            || func.name.starts_with("__module_init_")
            || func.name.starts_with("spl_")
            || func.name.starts_with("__get_global_")
            || func.name.starts_with("__set_global_");
        if keeps_abi_name {
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

    // `expand_with_outlined` (codegen/shared.rs, called by both the LLVM/AOT
    // and Cranelift/JIT backends) names a lambda's outlined body
    // `"{parent_func_name}_outlined_{block_id}"`, using the PARENT's name AT
    // OUTLINING TIME (i.e. after this mangling pass has already renamed the
    // parent, since outlining runs later, per-backend, in `compile()`).
    // `MirInst::ClosureCreate::func_name`, however, is baked at MIR-lowering
    // time using the parent's name BEFORE mangling — e.g. `main` becomes
    // `main_outlined_1`, but Phase 1 below renames the parent function itself
    // to `spl_main` (entry) or `{prefix}__main` (non-entry), so the outlined
    // function ends up defined as `spl_main_outlined_1` /
    // `{prefix}__main_outlined_1` while the closure still points at the
    // stale, never-defined `main_outlined_1`. `compile_closure_create`
    // (codegen/llvm/functions/objects.rs) silently falls back to a NULL
    // function pointer when `module.get_function(func_name)` misses, so
    // every call through that closure VALUE loaded and called a null
    // pointer — measured exit 133 (SIGTRAP) / 139 (SIGSEGV). Precompute the
    // old-prefix -> new-prefix rename table here, before Phase 1 mutates
    // `func.name`, so Phase 3 can rewrite `ClosureCreate::func_name` to match
    // the name the outlined function will actually be given.
    // See doc/08_tracking/bug/native_closure_value_indirect_call_segv_2026-09-07.md.
    let outlined_name_rename: Vec<(String, String)> = local_mangled
        .iter()
        .filter(|(old, new)| old.as_str() != new.as_str())
        .map(|(old, new)| (format!("{old}_outlined_"), format!("{new}_outlined_")))
        .collect();

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
        } else if !is_runtime_or_builtin(name) {
            if let Some(resolved) = resolve_name(
                name,
                &local_global_mangled,
                use_map,
                import_map,
                &local_suffix_index,
                suffix_index,
            ) {
                new_globals.push((resolved, *ty, *is_mut));
            } else {
                new_globals.push((name.clone(), *ty, *is_mut));
            }
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

    let old_init_arrays = std::mem::take(&mut mir.global_init_arrays);
    for (name, val) in old_init_arrays {
        if let Some(mangled) = local_global_mangled.get(&name) {
            mir.global_init_arrays.insert(mangled.clone(), val);
        } else {
            mir.global_init_arrays.insert(name, val);
        }
    }

    let old_init_functions = std::mem::take(&mut mir.global_init_functions);
    for (name, func_name) in old_init_functions {
        let global_name = local_global_mangled.get(&name).cloned().unwrap_or(name);
        let resolved_func = local_mangled
            .get(&func_name)
            .cloned()
            .or_else(|| use_map.get(&func_name).cloned())
            .or_else(|| import_map.get(&func_name).cloned())
            .or_else(|| {
                resolve_name(
                    &func_name,
                    &local_mangled,
                    use_map,
                    import_map,
                    &local_suffix_index,
                    suffix_index,
                )
            })
            .unwrap_or(func_name);
        mir.global_init_functions.insert(global_name, resolved_func);
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
        // Only the "." -> "_dot_" direction is safe to generate here: a
        // genuinely dot-bearing mangled name (e.g. the module-mangled
        // `Owner.method` form noted in `suffix_owner_matches`'s doc comment,
        // like `lib__common__target__PointerSize.bytes`) is rare and its
        // dot is always a real separator, so aliasing it to an underscored
        // spelling can't collide with anything.
        //
        // The REVERSE direction ("_dot_" -> ".") was removed: `set` holds
        // every mangled function name reachable from this compilation unit,
        // and "_dot_" is also an ordinary substring of plenty of real
        // identifiers with no dot-escape meaning at all (e.g.
        // `cosine_from_dot_and_magnitudes`). Generating a "." alias for
        // those inserted a PHANTOM entry
        // (`..._math_utils__cosine_from.and_magnitudes`) into `known_mangled`
        // that `canonicalize_equivalent_dot_name` then trusted as if it were
        // a real symbol, corrupting the call target and leaving it
        // undefined at the Stage-4 macOS final link (2026-09-07). No genuine
        // case needs this direction: a real `Owner_dot_method` MIR call
        // target whose dotted form is a real symbol already finds it
        // directly, because that dotted form is already IN the base `set`
        // (values are literal mangled names, not re-derived) -- the forward
        // alias above is what lets such a target be found via its
        // underscored spelling, and nothing here ever needs to invent a
        // dot out of an underscored name that never had one.
        let extras: Vec<String> = set
            .iter()
            .filter_map(|v| if v.contains('.') { Some(v.replace('.', "_dot_")) } else { None })
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
                        let mut canonical_name = target.name().to_string();
                        canonicalize_equivalent_dot_name(&mut canonical_name, &known_mangled);
                        if canonical_name != target.name() {
                            *target = target.with_name(canonical_name);
                        }
                        let name = target.name().to_string();
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
                        } else if is_runtime_or_builtin(&name) {
                            continue;
                        } else if let Some(resolved) = use_map.get(&name) {
                            *target = target.with_name(resolved.clone());
                        } else if !is_enum_helper_method(&name) {
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
                                ambiguous_names,
                                &local_suffix_index,
                                suffix_index,
                                &func.name,
                                prefix,
                                &mut unresolved_count,
                            );
                        }
                    }
                    MirInst::ClosureCreate { func_name, .. } => {
                        // Rewrite the stale pre-mangling outlined name (see
                        // `outlined_name_rename` above) so it matches the
                        // name `expand_with_outlined` will later give the
                        // outlined function once it is actually emitted.
                        for (old_prefix, new_prefix) in &outlined_name_rename {
                            if let Some(suffix) = func_name.strip_prefix(old_prefix.as_str()) {
                                *func_name = format!("{new_prefix}{suffix}");
                                break;
                            }
                        }
                    }
                    MirInst::InterpCall { func_name, .. } => {
                        if let Some(mangled) = local_mangled.get(func_name.as_str()) {
                            *func_name = mangled.clone();
                            continue;
                        }
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
                        canonicalize_equivalent_dot_name(func_name, &known_mangled);
                        if let Some(mangled) = local_mangled.get(func_name.as_str()) {
                            *func_name = mangled.clone();
                            continue;
                        }
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
                        } else if !is_enum_helper_method(func_name.as_str()) {
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
    // `_dot_` is this backend's escape for a `.` inside a Simple identifier, so
    // the branch below rewrites `Type_dot_method` back to `Type.method`. A raw
    // runtime ABI symbol is not a Simple identifier and must never be rewritten:
    // `rt_numeric_dot_f64` (dot *product*, defined in libsimple_native_all.a and
    // the Rust libsimple_runtime.a) was being turned into `rt_numeric.f64`, a
    // name that is not a valid C identifier and that no archive can own. That
    // reached the Stage-4 link as
    //   Stage4 requested symbols have no archive owner: rt_numeric.f64
    // from the f64 dot-product loops in src/lib/common/search/types.spl and
    // src/app/office/sheets/formula.spl (macOS, 2026-09-06).
    //
    // `rt_` is the runtime ABI prefix throughout this repo and is never the
    // leading segment of a mangled Simple owner, so passing these through
    // verbatim is safe and keeps every other name on the existing path.
    if name.starts_with("rt_") {
        return local_map
            .get(name)
            .or_else(|| use_map.get(name))
            .or_else(|| import_map.get(name))
            .cloned()
            .or_else(|| Some(name.to_string()));
    }
    if let Some(mangled) = local_map.get(name) {
        Some(mangled.clone())
    } else if name.contains("_dot_") {
        let dotted = name.replace("_dot_", ".");
        if let Some(mangled) = local_map.get(&dotted) {
            Some(mangled.clone())
        } else if let Some(resolved) = use_map.get(&dotted) {
            Some(resolved.clone())
        } else if let Some(resolved) = import_map.get(&dotted) {
            Some(resolved.clone())
        } else {
            resolve_name_variants(name, use_map, import_map)
                .or_else(|| resolve_by_suffix(name, local_suffix_index))
                .or_else(|| resolve_by_suffix(name, suffix_index))
        }
    } else if name.contains('.') {
        let sanitized = name.replace('.', "_dot_");
        if let Some(mangled) = local_map.get(&sanitized) {
            Some(mangled.clone())
        } else if let Some(resolved) = use_map.get(&sanitized) {
            Some(resolved.clone())
        } else if let Some(resolved) = import_map.get(&sanitized) {
            Some(resolved.clone())
        } else {
            resolve_name_variants(name, use_map, import_map)
                .or_else(|| resolve_by_suffix(name, local_suffix_index))
                .or_else(|| resolve_by_suffix(name, suffix_index))
        }
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
#[allow(clippy::too_many_arguments)] // reason: call resolution requires full module context
fn resolve_call_target(
    target: &mut crate::mir::CallTarget,
    name: &str,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    ambiguous_names: &std::collections::HashSet<String>,
    local_suffix_index: &std::collections::HashMap<String, Vec<String>>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
    func_name: &str,
    prefix: &str,
    unresolved_count: &mut usize,
) {
    // Try the RAW name first. `_dot_` is only a genuine dot-escape marker for
    // names built by joining an "Owner" and "method" token; it is also, by
    // coincidence, an ordinary substring of plenty of real identifiers (e.g.
    // `cosine_from_dot_and_magnitudes`). Decoding it unconditionally before
    // any resolution attempt corrupted such names into
    // `cosine_from.and_magnitudes`, which then resolves to nothing and gets
    // emitted verbatim as an undefined call target -- the Stage-4 macOS
    // final link (2026-09-07) and, per the SIMD-kernel `rt_numeric_dot_f64`
    // -> `rt_numeric.f64` defect this mirrors, likely others historically.
    // A raw-name lookup is always correct for a genuine cross-module
    // function (use_map/import_map key it by the UNMODIFIED source
    // identifier), so try it before ever computing the decoded form.
    if let Some(resolved) = resolve_name_variants(name, use_map, import_map) {
        *target = target.with_name(resolved);
        return;
    }

    let lookup_name_storage;
    let lookup_name = if name.contains("_dot_") {
        lookup_name_storage = name.replace("_dot_", ".");
        lookup_name_storage.as_str()
    } else {
        name
    };

    if !lookup_name.contains('.')
        && matches!(
            lookup_name,
            "unwrap" | "unwrap_or" | "unwrap_err" | "is_some" | "is_none" | "is_ok" | "is_err"
        )
    {
        // Preserve bare enum-helper call targets so codegen can route them to the
        // runtime builtins. If we suffix-resolve bare `unwrap` here, ordinary
        // option-like field access in local code can be rebound to an imported
        // `FailSafeResult.unwrap` symbol, which is exactly the hosted RV64 leak
        // observed from Report.get_file/get_line/format and LevelConfig.effective_level.
        return;
    }

    if let Some(resolved) = resolve_name_variants(lookup_name, use_map, import_map) {
        *target = target.with_name(resolved);
    } else if lookup_name.contains('.') {
        let method = lookup_name.rsplit('.').next().unwrap_or(lookup_name);
        let type_part = lookup_name.split('.').next().unwrap_or("");
        let candidates = local_suffix_index
            .get(lookup_name)
            .or_else(|| suffix_index.get(lookup_name))
            .or_else(|| local_suffix_index.get(method))
            .or_else(|| suffix_index.get(method));
        if is_enum_helper_method(method) {
            // SECOND ROUTE for the `Poll.unwrap` rebind (2026-09-13). PR #750
            // guarded `mangle_mir`'s two bare scans and the str/text/string UFCS
            // arm in `resolve_method_call_static`; 208 sites survived because a
            // QUALIFIED `T.unwrap` reaches here instead, where `.get(method)`
            // discards the qualifier and the `candidates.len() == 1` arm below
            // (plus both `resolve_by_suffix` fall-throughs) binds it to the only
            // `unwrap` in the 877-unit closure regardless of receiver type.
            // `static_.init.unwrap()` in cranelift_codegen_adapter.spl is one
            // such site. For these names the only sound rebind is an exact owner
            // match; anything else must stay bare so codegen's `bare_rt_redirect`
            // lowering owns it, which is correct for every receiver shape.
            if let Some(b) = candidates.into_iter().flatten().find(|c| enum_helper_owner_matches(c, type_part)) {
                *target = target.with_name(b.clone());
            }
            return;
        }
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
            } else if let Some(resolved) = resolve_by_suffix(lookup_name, local_suffix_index)
                .or_else(|| resolve_by_suffix(lookup_name, suffix_index))
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
            resolve_by_suffix(lookup_name, local_suffix_index).or_else(|| resolve_by_suffix(lookup_name, suffix_index))
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
        resolve_ambiguous_private_call_in_module(lookup_name, prefix, ambiguous_names, suffix_index)
            .or_else(|| resolve_by_suffix(lookup_name, local_suffix_index))
            .or_else(|| resolve_by_suffix(lookup_name, suffix_index))
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

fn resolve_ambiguous_private_call_in_module(
    name: &str,
    prefix: &str,
    ambiguous_names: &std::collections::HashSet<String>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) -> Option<String> {
    if !name.starts_with('_') || !ambiguous_names.contains(name) {
        return None;
    }

    let suffix = format!("__{name}");
    let mut candidates = std::collections::BTreeSet::new();
    for candidate in suffix_index.values().flatten() {
        if candidate.ends_with(&suffix) {
            candidates.insert(candidate);
        }
    }

    let mut best = None;
    let mut best_score = 0;
    let mut tied = false;
    for candidate in candidates {
        let owner = candidate.strip_suffix(&suffix)?;
        let score = owner
            .split("__")
            .zip(prefix.split("__"))
            .take_while(|(left, right)| left == right)
            .count();
        if score > best_score {
            best = Some(candidate);
            best_score = score;
            tied = false;
        } else if score == best_score && score != 0 {
            tied = true;
        }
    }

    (best_score != 0 && !tied).then(|| best.unwrap().clone())
}

/// Resolve a MethodCallStatic target that is still unresolved.
fn resolve_method_call_static(
    func_name: &mut String,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
    local_suffix_index: &std::collections::HashMap<String, Vec<String>>,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) {
    // A raw runtime ABI symbol is not a mangled Simple identifier: `_dot_` in
    // it is literal, not an escaped `.`. Rewriting turned the SIMD reduction
    // kernel `rt_numeric_dot_f64` (dot *product*) into `rt_numeric.f64`, which
    // is not a valid C identifier and which no archive can own, failing the
    // Stage-4 link with "requested symbols have no archive owner:
    // rt_numeric.f64" (macOS, 2026-09-06). Leave `rt_*` exactly as emitted.
    if func_name.starts_with("rt_") {
        return;
    }
    let lookup_name_storage;
    let lookup_name = if func_name.contains("_dot_") {
        lookup_name_storage = func_name.replace("_dot_", ".");
        lookup_name_storage.as_str()
    } else {
        func_name.as_str()
    };

    // Collection `parts.join(sep)` lowers to a bare builtin call. An imported
    // path helper with the same name must not capture it during suffix binding.
    if matches!(lookup_name, "join" | "Array.join") {
        return;
    }

    // The string-builtin guard below must run BEFORE resolve_name_variants,
    // not only before the suffix fallback: a project-wide FREE function with a
    // builtin's name (private `fn char_at(s, i)` in mcp_sdk/core/json.spl) leaks
    // into the global import map as a bare entry, so resolution SUCCEEDS and
    // rebinds an erased-receiver `.char_at()` to a module that may not even be
    // in the entry closure (undefined `..mcp_sdk__core__json__char_at` at the
    // stage4 final link, 2026-07-25). For these names builtin lowering is the
    // correct semantics for every receiver, so pre-resolution is safe — same
    // rationale as the `join` guard above. The enum-helper and numeric lists
    // stay in the post-failure position: hoisting them broke legitimate
    // resolution-success rebinds (the compiled interpreter's own Option
    // helpers printed `<unknown>` for every text-option `??`, 2026-07-25).
    let method_early = lookup_name.rsplit('.').next().unwrap_or(lookup_name);
    if !lookup_name.contains('.') {
        if matches!(
            method_early,
            "starts_with"
                | "ends_with"
                | "trim"
                | "trim_start"
                | "trim_end"
                | "to_upper"
                | "upper"
                | "to_lower"
                | "lower"
                | "char_at"
                | "char_code_at"
                | "replace"
        ) {
            // Preserve bare string-builtin method names when the receiver type
            // could not be recovered (an erased receiver -- e.g. `parts[i]` from
            // `split(...)`, or a `line.trim()` chain -- leaves the MethodCallStatic
            // func_name bare). Rebinding bare `starts_with` to the ONLY user method
            // of that name, struct `Path.starts_with` (fs_driver/types.spl), whose
            // `self.raw` dereferences the text receiver as a Path struct, crashed
            // inside decode_string (SimpleOS WM first-frame render fault,
            // 2026-07-13). Leaving the name bare routes it through codegen's
            // `bare_rt_redirect` table (functions/calls.rs) -> rt_string_* -- the
            // SAME correct lowering a statically-typed `text` receiver gets. Every
            // method here has a bare_rt_redirect entry, so leaving it bare never
            // produces an unresolved-call error. Scoped to unambiguous string ops
            // (contains/split/index_of/to_string are intentionally excluded --
            // either they collide with generic user methods or lack a
            // bare_rt_redirect entry).
            return;
        }
    }

    if let Some(resolved) = resolve_name_variants(lookup_name, use_map, import_map) {
        *func_name = resolved;
    } else {
        let method = lookup_name.rsplit('.').next().unwrap_or(lookup_name);
        let type_part = lookup_name.split('.').next().unwrap_or("");
        let has_type_qualifier = lookup_name.contains('.');
        if !has_type_qualifier
            && matches!(
                method,
                "unwrap" | "unwrap_or" | "unwrap_err" | "is_some" | "is_none" | "is_ok" | "is_err"
            )
        {
            // Preserve enum helper method names when the receiver type could not be
            // recovered. Rebinding bare `unwrap` by suffix to an imported
            // `FailSafeResult.unwrap` symbol causes option/result-style field access
            // in local code (for example Report.location.unwrap()) to become a fake
            // cross-module call target instead of flowing through the builtin enum
            // payload/discriminant lowering paths.
            return;
        }
        if !has_type_qualifier
            && matches!(
                method,
                "len"
                    | "to_i8"
                    | "to_i16"
                    | "to_i32"
                    | "to_i64"
                    | "to_u8"
                    | "to_u16"
                    | "to_u32"
                    | "to_u64"
                    | "to_f32"
                    | "to_f64"
                    | "to_int"
                    | "to_float"
            )
        {
            // Same defect class as the string-builtin guard above, for NUMERIC
            // builtins: a bare erased-receiver `.to_i32()` (e.g. `value.len()
            // .to_i32()`, `commands.len().to_i32()`) must lower to the builtin
            // conversion, not rebind through the single-candidate suffix
            // fallback to the ONLY user method of that name (`Px.to_i32`,
            // window_protocol/geometry.spl), which would deref the raw integer
            // as a Px pointer -> null-receiver fault on the SimpleOS WM
            // first-frame render (cr2=0, 2026-07-17). Leaving the name bare
            // routes it through codegen's builtin numeric lowering (a direct
            // truncation/extension), which is the correct semantics for every
            // primitive receiver.
            return;
        }
        let type_part_lower = type_part.to_lowercase();
        let candidates = local_suffix_index.get(method).or_else(|| suffix_index.get(method));
        if is_enum_helper_method(method) {
            // Qualified enum helpers: exact owner match only. The generic
            // `contains(&type_part_lower)` arm below is a substring test against
            // the FULL mangled path, so `T.unwrap` / `Mut.unwrap` /
            // `Async.unwrap` all match
            // `lib__nogc_async_mut__async__poll__Poll.unwrap` by accident. Same
            // defect class and same remedy as the guard in
            // `resolve_call_target`; the str/text/string arm further down keeps
            // its own `!is_enum_helper_method` check as a belt-and-braces
            // statement of the same invariant.
            if let Some(b) = candidates.into_iter().flatten().find(|c| enum_helper_owner_matches(c, type_part)) {
                *func_name = b.clone();
            }
            return;
        }
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
                // A qualified receiver is semantic type evidence.  Do not
                // discard it merely because another type contributes the only
                // same-named method in the suffix index (for example,
                // `str.rfind` versus `DoubleEndedIterator.rfind`).  Bare calls
                // have no such evidence and retain the unique-candidate
                // fallback.
                if !has_type_qualifier && candidates.len() == 1 {
                    candidates.first()
                } else {
                    None
                }
            });
            let best = best.or_else(|| {
                // Text UFCS gap (Stage-4 macOS final link, 2026-09-07): a
                // qualified `str.split_whitespace` / `str.index_of_from` never
                // matches the `contains(&type_part_lower)` owner filter above
                // because the real definition lives in an unrelated module
                // (`lib/common/text_advanced.spl`, `sffi_gen/intern_codegen.spl`)
                // whose mangled path does not literally contain "str" — these
                // are plain top-level `fn f(text, ...)` functions called via
                // UFCS on a text receiver, not methods of a type named "str".
                // Scoped to the STRING type aliases only (never widens generic
                // type-qualified matching, which stays strict to avoid the
                // `str.rfind`-vs-`DoubleEndedIterator.rfind` ambiguity above),
                // and only when there is a single unambiguous candidate.
                // NEVER for the Optional/Result helper names (macOS Stage 2
                // linker blocker, 2026-09-13). `find_mold_path() -> text?`
                // followed by `mold_path.unwrap()` reaches here as
                // `text.unwrap` — a qualifier naming the PAYLOAD type, not a
                // type that owns an `unwrap` method. In the 877-unit Stage 2
                // closure the suffix index holds exactly ONE `unwrap`
                // candidate, `lib__nogc_async_mut__async__poll__Poll.unwrap`,
                // so this single-candidate arm rebound the call to it and
                // `Ok(mold_path.unwrap())` was constructed with the INTEGER 0.
                // `darwin_resolve_link_tool(0)` then failed `file_exists` and
                // the hello-world link died as `Linking failed: no error
                // payload from link_to_native`. A 1-unit reproducer cannot
                // show it: `Poll.unwrap` is not in a small closure, so there
                // is no candidate to rebind to. These names must reach
                // codegen's builtin enum payload/discriminant lowering, which
                // is what the bare-receiver guard above already relies on.
                if has_type_qualifier
                    && matches!(type_part_lower.as_str(), "str" | "text" | "string")
                    && !is_enum_helper_method(method)
                    && candidates.len() == 1
                {
                    candidates.first()
                } else {
                    None
                }
            });
            if let Some(b) = best {
                *func_name = b.clone();
            }
        } else if let Some(resolved) =
            resolve_by_suffix(lookup_name, local_suffix_index).or_else(|| resolve_by_suffix(lookup_name, suffix_index))
        {
            *func_name = resolved;
        }
    }
}

fn canonicalize_equivalent_dot_name(name: &mut String, known_mangled: &std::collections::HashSet<String>) {
    if name.contains("_dot_") {
        let dotted = name.replace("_dot_", ".");
        if known_mangled.contains(dotted.as_str()) {
            *name = dotted;
        }
    }
}

/// Check if a name is a runtime/builtin that should never be mangled.
fn is_runtime_or_builtin_name(name: &str, extern_fns: &std::collections::HashSet<String>) -> bool {
    extern_fns.contains(name)
        || name.starts_with("rt_")
        || name.starts_with("__simple_")
        || name.starts_with("__module_init_")
        || name.starts_with("spl_")
        || name.starts_with("__get_global_")
        || name.starts_with("__set_global_")
        || name.starts_with("bit_")
        || name.starts_with("bitwise_")
        || name.starts_with("sffi_")
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

#[cfg(test)]
mod tests {
    use super::{enum_helper_owner_matches, is_enum_helper_method, resolve_call_target, resolve_method_call_static};
    use crate::mir::CallTarget;
    use std::collections::HashMap;

    fn poll_index() -> HashMap<String, Vec<String>> {
        HashMap::from([(
            "unwrap".to_string(),
            vec!["lib__nogc_async_mut__async__poll__Poll.unwrap".to_string()],
        )])
    }

    fn run_call_target(name: &str, suffix_index: &HashMap<String, Vec<String>>) -> String {
        let mut target = CallTarget::Pure(name.to_string());
        let mut unresolved = 0usize;
        resolve_call_target(
            &mut target,
            name,
            &HashMap::new(),
            &HashMap::new(),
            &std::collections::HashSet::new(),
            &HashMap::new(),
            suffix_index,
            "caller",
            "prefix",
            &mut unresolved,
        );
        target.name().to_string()
    }

    fn run_method_static(name: &str, suffix_index: &HashMap<String, Vec<String>>) -> String {
        let mut out = name.to_string();
        resolve_method_call_static(&mut out, &HashMap::new(), &HashMap::new(), &HashMap::new(), suffix_index);
        out
    }

    /// Route 2 of the `Poll.unwrap` rebind (2026-09-13): a QUALIFIED helper
    /// call reaching `resolve_call_target`, whose candidate lookup discards the
    /// qualifier and whose `candidates.len() == 1` arm then binds any receiver
    /// to the lone `unwrap` in the closure. `static_.init.unwrap()` in
    /// cranelift_codegen_adapter.spl is a real site of exactly this shape.
    #[test]
    fn qualified_enum_helpers_never_rebind_in_resolve_call_target() {
        let idx = poll_index();
        for receiver in ["MirStaticInit", "T", "Mut", "Async", "Lib", "Wrap", "i64", "text"] {
            let name = format!("{receiver}.unwrap");
            assert_eq!(run_call_target(&name, &idx), name, "{name} must stay bare");
        }
        // The genuine owner still resolves, so the guard is not vacuous.
        assert_eq!(
            run_call_target("Poll.unwrap", &idx),
            "lib__nogc_async_mut__async__poll__Poll.unwrap"
        );
        // A non-helper method keeps today's single-candidate behaviour.
        let other = HashMap::from([("render".to_string(), vec!["lib__ui__widget__Widget.render".to_string()])]);
        assert_eq!(run_call_target("Button.render", &other), "lib__ui__widget__Widget.render");
    }

    /// Route 3: the same shape reaching `resolve_method_call_static`, where the
    /// surviving hole was `find(|c| c.to_lowercase().contains(&type_part_lower))`
    /// -- a substring test against the FULL mangled path, which
    /// `lib__nogc_async_mut__async__poll__Poll.unwrap` satisfies for most short
    /// type names.
    #[test]
    fn qualified_enum_helpers_never_substring_match_in_method_call_static() {
        let idx = poll_index();
        for receiver in ["T", "Mut", "Async", "Lib", "Wrap", "As", "MirStaticInit"] {
            for helper in ["unwrap", "is_some", "is_ok"] {
                let name = format!("{receiver}.{helper}");
                let idx = if helper == "unwrap" {
                    idx.clone()
                } else {
                    HashMap::from([(
                        helper.to_string(),
                        vec![format!("lib__nogc_async_mut__async__poll__Poll.{helper}")],
                    )])
                };
                assert_eq!(run_method_static(&name, &idx), name, "{name} must stay bare");
            }
        }
        assert_eq!(
            run_method_static("Poll.unwrap", &idx),
            "lib__nogc_async_mut__async__poll__Poll.unwrap"
        );
    }

    #[test]
    fn enum_helper_owner_match_is_exact_not_substring() {
        let poll = "lib__nogc_async_mut__async__poll__Poll.unwrap";
        assert!(enum_helper_owner_matches(poll, "Poll"));
        assert!(enum_helper_owner_matches(poll, "poll"));
        for wrong in ["T", "Mut", "Async", "Lib", "Wrap", "Pol", "PollX"] {
            assert!(!enum_helper_owner_matches(poll, wrong), "{wrong} must not match");
        }
        // An unqualified candidate (a free function) owns no type.
        assert!(!enum_helper_owner_matches("lib__tooling__notify__unwrap_or", "notify"));
    }

    #[test]
    fn array_join_stays_builtin_when_path_join_is_imported() {
        let use_map = HashMap::from([("join".to_string(), "nogc_async_mut__path__join".to_string())]);

        for builtin in ["join", "Array.join"] {
            let mut name = builtin.to_string();
            resolve_method_call_static(&mut name, &use_map, &HashMap::new(), &HashMap::new(), &HashMap::new());
            assert_eq!(name, builtin);
        }
    }

    /// macOS Stage 2 linker blocker, 2026-09-13.
    ///
    /// `mold_path.unwrap()` on a `text?` arrives here as `text.unwrap`. The
    /// Stage 2 closure contributes exactly one `unwrap` candidate,
    /// `Poll.unwrap`, and the str/text/string single-candidate UFCS arm bound
    /// the call to it; `Ok(mold_path.unwrap())` then carried the integer 0.
    /// The enum helpers must stay bare so codegen lowers them as builtins.
    #[test]
    fn text_qualified_enum_helpers_never_rebind_to_a_lone_user_method() {
        let poll_unwrap = "lib__nogc_async_mut__async__poll__Poll.unwrap".to_string();
        let suffix_index = HashMap::from([
            ("unwrap".to_string(), vec![poll_unwrap]),
            (
                "split_whitespace".to_string(),
                vec!["lib__common__text_advanced__split_whitespace".to_string()],
            ),
        ]);

        for helper in ["unwrap", "unwrap_or", "unwrap_err", "is_some", "is_none", "is_ok", "is_err"] {
            for receiver in ["str", "text", "string"] {
                let mut name = format!("{receiver}.{helper}");
                resolve_method_call_static(
                    &mut name,
                    &HashMap::new(),
                    &HashMap::new(),
                    &HashMap::new(),
                    &suffix_index,
                );
                assert_eq!(name, format!("{receiver}.{helper}"), "{receiver}.{helper} must stay bare");
            }
        }

        // The genuine text-UFCS rebind this arm exists for must still happen,
        // so the guard above cannot be satisfied by disabling the whole arm.
        let mut ufcs = "str.split_whitespace".to_string();
        resolve_method_call_static(
            &mut ufcs,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            &suffix_index,
        );
        assert_eq!(ufcs, "lib__common__text_advanced__split_whitespace");
    }

    /// The blocker itself. `mold_path.unwrap()` on a `text?` lowers to a BARE
    /// `unwrap` call target, and `mangle_mir`'s two bare `.method` scans (one
    /// for `MirInst::Call`, one for `MethodCallStatic`) rebound it to the only
    /// `.unwrap` entry in the import maps. Those scans are inline in a function
    /// that takes a whole `MirModule`, so this asserts the guard at source
    /// level -- the same technique the LLVM redirect-table invariant uses, and
    /// the reason a partial fix survived: guarding only the resolvers left the
    /// scans that run BEFORE them wide open.
    #[test]
    fn bare_enum_helper_scans_are_guarded_in_mangle_mir() {
        let src = include_str!("mangle.rs");

        for guard in [
            "} else if !is_enum_helper_method(&name) {",
            "} else if !is_enum_helper_method(func_name.as_str()) {",
        ] {
            assert!(src.contains(guard), "bare `.method` scan lost its guard: {guard}");
        }

        // Every helper the builtin lowering owns must be covered, and a name it
        // does not own must not be, so the predicate cannot pass vacuously.
        for helper in ["unwrap", "unwrap_or", "unwrap_err", "is_some", "is_none", "is_ok", "is_err"] {
            assert!(is_enum_helper_method(helper), "{helper} must be treated as a builtin helper");
        }
        assert!(!is_enum_helper_method("len"));
        assert!(!is_enum_helper_method("to_string"));
    }
}
