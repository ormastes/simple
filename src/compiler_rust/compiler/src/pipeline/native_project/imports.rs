//! Import map building, symbol resolution, module resolver integration.

use std::path::{Path, PathBuf};

use crate::codegen::common_backend::module_prefix_from_path;
use super::{safe_canonicalize, source_root_for_file};

/// Import map build result.
pub(crate) struct ImportMapResult {
    /// raw name -> mangled name (unique entries get direct mapping, ambiguous pick first)
    pub map: std::collections::HashMap<String, String>,
    /// Set of raw names with multiple definitions
    pub ambiguous: std::collections::HashSet<String>,
    /// raw name -> all mangled names (for per-module `use` statement resolution)
    pub all_mangled: std::collections::HashMap<String, Vec<String>>,
    /// module_prefix -> (func_name -> actual_mangled_name) for re-exported functions.
    pub re_exports: std::collections::HashMap<String, std::collections::HashMap<String, String>>,
    /// Global struct definitions: struct_name -> field names (in order).
    pub struct_defs: std::collections::HashMap<String, Vec<(String, String)>>,
}

/// Sanitize a mangled symbol name for the host platform.
fn sanitize_mangled(name: String) -> String {
    if name.contains('.') {
        name.replace('.', "_dot_")
    } else {
        name
    }
}

/// Try alternate name forms to resolve a call target through use_map/import_map.
pub(crate) fn resolve_name_variants(
    name: &str,
    use_map: &std::collections::HashMap<String, String>,
    import_map: &std::collections::HashMap<String, String>,
) -> Option<String> {
    if name.contains("_dot_") {
        let dotted = name.replace("_dot_", ".");
        if let Some(resolved) = use_map.get(&dotted).or_else(|| import_map.get(&dotted)) {
            return Some(resolved.clone());
        }
    }
    if let Some(pos) = name.find("__") {
        let type_part = &name[..pos];
        let method_part = &name[pos + 2..];
        let dotted = format!("{}.{}", type_part, method_part);
        if let Some(resolved) = use_map.get(&dotted).or_else(|| import_map.get(&dotted)) {
            return Some(resolved.clone());
        }
        let lower_joined = format!("{}_{}", type_part.to_lowercase(), method_part);
        if let Some(resolved) = use_map.get(&lower_joined).or_else(|| import_map.get(&lower_joined)) {
            return Some(resolved.clone());
        }
        let lower_no_sep = format!("{}{}", type_part.to_lowercase(), method_part.to_lowercase());
        if let Some(resolved) = import_map.get(&lower_no_sep) {
            return Some(resolved.clone());
        }
    }
    if let Some(pos) = name.find('.') {
        let underscored = format!("{}__{}", &name[..pos], &name[pos + 1..]);
        if let Some(resolved) = use_map.get(&underscored).or_else(|| import_map.get(&underscored)) {
            return Some(resolved.clone());
        }
        let all_under = name.replace('.', "__");
        if all_under != underscored {
            if let Some(resolved) = use_map.get(&all_under).or_else(|| import_map.get(&all_under)) {
                return Some(resolved.clone());
            }
        }
        let func_part = &name[pos + 1..];
        if !func_part.is_empty() {
            if let Some(resolved) = use_map.get(func_part).or_else(|| import_map.get(func_part)) {
                return Some(resolved.clone());
            }
        }
    }
    // Try enum variant constructor pattern
    for (i, _) in name.match_indices('_').rev() {
        let variant = &name[i + 1..];
        if variant.is_empty() {
            continue;
        }
        if !variant.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            continue;
        }
        let prefix_raw = &name[..i];
        if prefix_raw.is_empty() {
            continue;
        }
        for (key, resolved) in import_map.iter().chain(use_map.iter()) {
            if let Some(dot_pos) = key.rfind('.') {
                let key_variant = &key[dot_pos + 1..];
                let key_type = &key[..dot_pos];
                if key_variant == variant
                    && key_type.to_lowercase().replace("_", "") == prefix_raw.to_lowercase().replace("_", "")
                {
                    return Some(resolved.clone());
                }
            }
        }
    }
    None
}

pub(crate) fn suffix_of(name: &str) -> Option<&str> {
    if let Some((_, suffix)) = name.rsplit_once("__") {
        Some(suffix)
    } else if let Some((_, suffix)) = name.rsplit_once('.') {
        Some(suffix)
    } else {
        None
    }
}

/// Build a suffix index from all mangled names for fuzzy method resolution.
pub(crate) fn build_suffix_index(
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
) -> std::collections::HashMap<String, Vec<String>> {
    let mut index: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    for mangled_list in all_mangled.values() {
        for mangled in mangled_list {
            if let Some(suffix) = suffix_of(mangled) {
                index.entry(suffix.to_string()).or_default().push(mangled.clone());
                if let Some(dot_pos) = suffix.rfind('.') {
                    let sub_suffix = &suffix[dot_pos + 1..];
                    if !sub_suffix.is_empty() && sub_suffix.starts_with(|c: char| c.is_ascii_uppercase()) {
                        index.entry(sub_suffix.to_string()).or_default().push(mangled.clone());
                    }
                }
            }
        }
    }
    index
}

/// Resolve an unresolved call name by suffix matching against the suffix index.
pub(crate) fn resolve_by_suffix(name: &str, suffix_index: &std::collections::HashMap<String, Vec<String>>) -> Option<String> {
    if let Some(candidates) = suffix_index.get(name) {
        if candidates.len() == 1 {
            return Some(candidates[0].clone());
        }
    }
    for (i, _) in name.match_indices('_').rev() {
        let prefix = &name[..i];
        let method = &name[i + 1..];
        if method.is_empty() || prefix.is_empty() {
            continue;
        }

        if let Some(candidates) = suffix_index.get(method) {
            if candidates.len() == 1 {
                return Some(candidates[0].clone());
            }
            let prefix_lower = prefix.to_lowercase();
            let matching: Vec<_> = candidates
                .iter()
                .filter(|c| c.to_lowercase().contains(&prefix_lower))
                .collect();
            if matching.len() == 1 {
                return Some(matching[0].clone());
            }
            if !matching.is_empty() {
                if let Some(best) = matching.iter().min_by_key(|c| c.len()) {
                    return Some((*best).clone());
                }
            }
        }
    }
    None
}

/// Build an import map for cross-module function resolution.
pub(crate) fn build_import_map(file_sources: &[(PathBuf, String)], source_dirs: &[PathBuf], fallback_root: &Path) -> ImportMapResult {
    use std::collections::{HashMap, HashSet};

    let mut raw_to_mangled: HashMap<String, Vec<String>> = HashMap::new();
    let mut struct_defs: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let mut seen_canonical = HashSet::new();
    for (path, source) in file_sources {
        if path.to_string_lossy().contains("check.spl") {
            continue;
        }
        let canonical_path = safe_canonicalize(path);
        if !seen_canonical.insert(canonical_path) {
            continue;
        }
        let per_file_root = source_root_for_file(path, source_dirs, fallback_root);
        let prefix = module_prefix_from_path(path, &per_file_root);
        let mut parser = simple_parser::Parser::new(source);
        if let Ok(ast) = parser.parse() {
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::Function(f) => {
                        if !f.body.statements.is_empty() {
                            let mangled = format!("{}__{}", prefix, f.name);
                            raw_to_mangled.entry(f.name.clone()).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Class(c) => {
                        if !c.fields.is_empty() {
                            let fields: Vec<(String, String)> = c.fields.iter().map(|f| {
                                let ty_name = format!("{:?}", f.ty);
                                (f.name.clone(), ty_name)
                            }).collect();
                            struct_defs.entry(c.name.clone()).or_insert(fields);
                        }
                        for m in &c.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", c.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, c.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    simple_parser::ast::Node::Extern(e) => {
                        let mangled = e.name.clone();
                        raw_to_mangled.entry(e.name.clone()).or_default().push(mangled);
                    }
                    simple_parser::ast::Node::ExternClass(ec) => {
                        for m in &ec.methods {
                            let raw = format!("{}.{}", ec.name, m.name);
                            let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, ec.name, m.name));
                            raw_to_mangled.entry(raw.clone()).or_default().push(mangled.clone());
                            raw_to_mangled.entry(m.name.clone()).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Let(l) => {
                        if let Some(name) = extract_let_name(&l.pattern) {
                            let mangled = format!("{}__{}", prefix, name);
                            raw_to_mangled.entry(name).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Const(c) => {
                        let mangled = format!("{}__{}", prefix, c.name);
                        raw_to_mangled.entry(c.name.clone()).or_default().push(mangled);
                    }
                    simple_parser::ast::Node::Static(s) => {
                        let mangled = format!("{}__{}", prefix, s.name);
                        raw_to_mangled.entry(s.name.clone()).or_default().push(mangled);
                    }
                    simple_parser::ast::Node::Struct(s) => {
                        if !s.fields.is_empty() {
                            let fields: Vec<(String, String)> = s.fields.iter().map(|f| {
                                let ty_name = format!("{:?}", f.ty);
                                (f.name.clone(), ty_name)
                            }).collect();
                            struct_defs.entry(s.name.clone()).or_insert(fields);
                        }
                        for m in &s.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", s.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, s.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    simple_parser::ast::Node::Enum(e) => {
                        for m in &e.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", e.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, e.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                        for v in &e.variants {
                            let raw = format!("{}.{}", e.name, v.name);
                            let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, e.name, v.name));
                            raw_to_mangled.entry(raw).or_default().push(mangled);
                            if let Some(ref fields) = v.fields {
                                let named: Vec<(String, String)> = fields.iter()
                                    .filter_map(|f| f.name.as_ref().map(|n| {
                                        let ty_name = format!("{:?}", f.ty);
                                        (n.clone(), ty_name)
                                    }))
                                    .collect();
                                if !named.is_empty() {
                                    struct_defs.entry(v.name.clone()).or_insert(named);
                                }
                            }
                        }
                    }
                    simple_parser::ast::Node::Trait(t) => {
                        for m in &t.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", t.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, t.name, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    simple_parser::ast::Node::Impl(imp) => {
                        let type_name = match &imp.target_type {
                            simple_parser::ast::Type::Simple(n) => Some(n.as_str()),
                            simple_parser::ast::Type::Generic { name, .. } => Some(name.as_str()),
                            _ => None,
                        };
                        if let Some(type_name) = type_name {
                            for m in &imp.methods {
                                if !m.body.statements.is_empty() {
                                    let raw = format!("{}.{}", type_name, m.name);
                                    let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, type_name, m.name));
                                    raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                    raw_to_mangled.entry(raw).or_default().push(mangled);
                                }
                            }
                        }
                    }
                    simple_parser::ast::Node::Extend(ext) => {
                        for m in &ext.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", ext.target_type, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, ext.target_type, m.name));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let mut map = std::collections::HashMap::new();
    let mut ambiguous = std::collections::HashSet::new();
    for (raw, mangled_list) in &raw_to_mangled {
        if mangled_list.len() == 1 {
            map.insert(raw.clone(), mangled_list[0].clone());
        } else {
            ambiguous.insert(raw.clone());
            map.insert(raw.clone(), mangled_list[0].clone());
        }
    }

    // Build re-export index
    let mut re_exports: std::collections::HashMap<String, std::collections::HashMap<String, String>> = std::collections::HashMap::new();
    let mut seen_canonical_reexport = std::collections::HashSet::new();
    for (path, source) in file_sources {
        let canonical_path = safe_canonicalize(path);
        if !seen_canonical_reexport.insert(canonical_path) {
            continue;
        }
        let per_file_root = source_root_for_file(path, source_dirs, fallback_root);
        let prefix = module_prefix_from_path(path, &per_file_root);
        let mut parser = simple_parser::Parser::new(source);
        if let Ok(ast) = parser.parse() {
            let mut use_items: Vec<(Vec<String>, &simple_parser::ast::ImportTarget)> = Vec::new();
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::UseStmt(u) => {
                        use_items.push((u.path.segments.clone(), &u.target));
                    }
                    simple_parser::ast::Node::MultiUse(mu) => {
                        for (path, target) in &mu.imports {
                            use_items.push((path.segments.clone(), target));
                        }
                    }
                    _ => {}
                }
            }
            for (segments, target) in use_items {
                let norm_segments: Vec<&str> = segments
                    .iter()
                    .map(|s| if s == "std" { "lib" } else { s.as_str() })
                    .collect();
                let names = collect_imported_names_flat(target);
                for name in names {
                    if let Some(candidates) = raw_to_mangled.get(&name) {
                        let resolved = if candidates.len() == 1 {
                            candidates[0].clone()
                        } else {
                            candidates
                                .iter()
                                .find(|c| mangled_matches_use_path(c, &norm_segments))
                                .cloned()
                                .unwrap_or_else(|| candidates[0].clone())
                        };
                        re_exports.entry(prefix.clone()).or_default().insert(name, resolved);
                    }
                }
            }
        }
    }

    // Hardcode critical logging symbols
    let logger_debug = sanitize_mangled("compiler__common__config__Logger.debug".to_string());
    map.entry("Logger.debug".to_string()).or_insert_with(|| logger_debug.clone());
    map.entry("debug".to_string()).or_insert_with(|| logger_debug.clone());

    let logger_trace = sanitize_mangled("compiler__common__config__Logger.trace".to_string());
    map.entry("Logger.trace".to_string()).or_insert_with(|| logger_trace.clone());
    map.entry("trace".to_string()).or_insert_with(|| logger_trace.clone());

    let boot_debug = sanitize_mangled("compiler__driver__driver_types__BootLogger.debug".to_string());
    map.entry("BootLogger.debug".to_string()).or_insert_with(|| boot_debug.clone());

    let boot_trace = sanitize_mangled("compiler__driver__driver_types__BootLogger.trace".to_string());
    map.entry("BootLogger.trace".to_string()).or_insert_with(|| boot_trace.clone());

    let driver_compile = sanitize_mangled("compiler__driver__driver__CompilerDriver.compile".to_string());
    map.entry("CompilerDriver.compile".to_string()).or_insert_with(|| driver_compile.clone());

    let compile_result_get_errors =
        sanitize_mangled("compiler__driver__driver_types__CompileResult.get_errors".to_string());
    map.entry("CompileResult.get_errors".to_string()).or_insert_with(|| compile_result_get_errors.clone());
    map.entry("get_errors".to_string()).or_insert_with(|| compile_result_get_errors.clone());

    ImportMapResult {
        map,
        ambiguous,
        all_mangled: raw_to_mangled,
        re_exports,
        struct_defs,
    }
}

/// Build a per-module use map from AST `use` statements.
pub(crate) fn build_use_map_from_ast(
    ast: &simple_parser::ast::Module,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> std::collections::HashMap<String, String> {
    let mut use_map = std::collections::HashMap::new();

    for item in &ast.items {
        match item {
            simple_parser::ast::Node::UseStmt(use_stmt) => {
                collect_use_imports(
                    &use_stmt.path.segments,
                    &use_stmt.target,
                    all_mangled,
                    re_exports,
                    &mut use_map,
                );
            }
            simple_parser::ast::Node::ExportUseStmt(export_use) => {
                collect_use_imports(
                    &export_use.path.segments,
                    &export_use.target,
                    all_mangled,
                    re_exports,
                    &mut use_map,
                );
            }
            simple_parser::ast::Node::MultiUse(multi_use) => {
                for (path, target) in &multi_use.imports {
                    collect_use_imports(&path.segments, target, all_mangled, re_exports, &mut use_map);
                }
            }
            _ => {}
        }
    }

    use_map
}

fn collect_use_imports(
    path_segments: &[String],
    target: &simple_parser::ast::ImportTarget,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
    use_map: &mut std::collections::HashMap<String, String>,
) {
    let segments: Vec<&str> = path_segments
        .iter()
        .map(|s| if s == "std" { "lib" } else { s.as_str() })
        .collect();

    match target {
        simple_parser::ast::ImportTarget::Single(name) => {
            if let Some(mangled) = resolve_import_name(name, &segments, all_mangled, re_exports) {
                use_map.insert(name.clone(), mangled);
            }
            let prefix = format!("{}.", name);
            for (raw_name, _candidates) in all_mangled.iter() {
                if raw_name.starts_with(&prefix) {
                    if let Some(mangled) = resolve_import_name(raw_name, &segments, all_mangled, re_exports) {
                        use_map.insert(raw_name.clone(), mangled);
                    }
                }
            }
        }
        simple_parser::ast::ImportTarget::Aliased { name, alias } => {
            if let Some(mangled) = resolve_import_name(name, &segments, all_mangled, re_exports) {
                use_map.insert(alias.clone(), mangled);
            }
        }
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                collect_use_imports(path_segments, item, all_mangled, re_exports, use_map);
            }
        }
        simple_parser::ast::ImportTarget::Glob => {}
    }
}

fn resolve_import_name(
    func_name: &str,
    use_segments: &[&str],
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> Option<String> {
    let candidates = all_mangled.get(func_name)?;
    if candidates.len() == 1 {
        return Some(candidates[0].clone());
    }

    for candidate in candidates {
        if mangled_matches_use_path(candidate, use_segments) {
            return Some(candidate.clone());
        }
    }

    let expected_prefix = use_segments.join("__");
    if let Some(module_re_exports) = re_exports.get(&expected_prefix) {
        if let Some(actual_mangled) = module_re_exports.get(func_name) {
            return Some(actual_mangled.clone());
        }
    }

    if use_segments.len() > 1 {
        let stripped_prefix = use_segments[1..].join("__");
        if let Some(module_re_exports) = re_exports.get(&stripped_prefix) {
            if let Some(actual_mangled) = module_re_exports.get(func_name) {
                return Some(actual_mangled.clone());
            }
        }
    }

    Some(candidates[0].clone())
}

fn collect_imported_names_flat(target: &simple_parser::ast::ImportTarget) -> Vec<String> {
    let mut names = Vec::new();
    match target {
        simple_parser::ast::ImportTarget::Single(name) => names.push(name.clone()),
        simple_parser::ast::ImportTarget::Aliased { name, .. } => names.push(name.clone()),
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                names.extend(collect_imported_names_flat(item));
            }
        }
        simple_parser::ast::ImportTarget::Glob => {}
    }
    names
}

fn mangled_matches_use_path(mangled: &str, use_segments: &[&str]) -> bool {
    let parts: Vec<&str> = mangled.split("__").collect();
    if subsequence_match_parts(&parts, use_segments) {
        return true;
    }
    if use_segments.len() > 1 {
        return subsequence_match_parts(&parts, &use_segments[1..]);
    }
    false
}

fn subsequence_match_parts(parts: &[&str], segments: &[&str]) -> bool {
    let mut seg_idx = 0;
    for part in parts {
        if seg_idx < segments.len() && *part == segments[seg_idx] {
            seg_idx += 1;
        }
    }
    seg_idx == segments.len()
}

/// Extract variable name from a Let statement's pattern.
fn extract_let_name(pattern: &simple_parser::Pattern) -> Option<String> {
    match pattern {
        simple_parser::Pattern::Identifier(n) => Some(n.clone()),
        simple_parser::Pattern::MutIdentifier(n) => Some(n.clone()),
        simple_parser::Pattern::Typed { pattern: inner, .. } => extract_let_name(inner),
        _ => None,
    }
}
