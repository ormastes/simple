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
    /// Project-wide `impl Trait for Type` declarations. MIR lowering uses this
    /// to distinguish real cross-module vtable dispatch from unsupported
    /// duck-typed calls.
    pub trait_impls: std::collections::HashMap<String, Vec<String>>,
    /// Global struct definitions: struct_name -> field names (in order).
    pub struct_defs: std::collections::HashMap<String, Vec<(String, simple_parser::Type)>>,
    /// Duplicate global struct/class definitions keyed by bare type name.
    /// Each entry preserves the full field layout for every colliding
    /// definition so the HIR lowerer can disambiguate field lookups by the
    /// requested field name instead of relying on the lossy first-wins map.
    pub duplicate_struct_defs: std::collections::HashMap<String, Vec<Vec<(String, simple_parser::Type)>>>,
    /// Global enum definitions with their payload field types.
    ///
    /// W15-H: this fixes class-1 of the HIR ANY-field bug — TitleCase enum
    /// receivers (`TypeKind`, `TokenKind`, etc.) referenced in a compilation
    /// unit that does not transitively reach them via a `use` chain were
    /// missing from `module.types.name_to_id`, so `lookup(recv_name)` in
    /// `expr/access.rs::lower_field_access` returned None and the
    /// enum-variant early-return fell through to the field-access fallback.
    pub enum_defs: std::collections::HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>>,
    /// Set of mangled names that correspond to module-level `val`/`var`/`const`
    /// (i.e. DATA, not functions). Used by the cranelift backend to decide
    /// whether a cross-module imported global should be declared as a data
    /// import (read value from memory) or a function import (load function
    /// address). Without this set, data constants imported across modules
    /// get incorrectly routed through the function-import fast path and
    /// `GlobalLoad` returns the symbol's address instead of its value.
    pub data_exports: std::collections::HashSet<String>,
    /// Mangled function name → declared parameter count. Used by the codegen
    /// backend to strip the spurious nil receiver that HIR→MIR lowering adds
    /// to module-qualified free function calls (`mod.func(args)` → MIR args
    /// `[nil, args...]`). Without this, the cross-module import signature is
    /// built from `arg_vals.len()` which includes the nil, causing the callee
    /// to receive nil in its first register instead of the real argument.
    pub fn_arities: std::collections::HashMap<String, usize>,
    pub fn_return_types: std::collections::HashMap<String, simple_parser::Type>,
}

/// Sanitize a mangled symbol name for the host platform.
fn sanitize_mangled(name: String) -> String {
    if name.contains('.') {
        name.replace('.', "_dot_")
    } else {
        name
    }
}

fn has_concrete_body(body: &simple_parser::ast::Block) -> bool {
    !body.statements.is_empty() && !matches!(body.statements.as_slice(), [simple_parser::ast::Node::Pass(_)])
}

fn method_arity(method: &simple_parser::ast::FunctionDef) -> usize {
    method.params.len() + usize::from(!method.is_static && !method.params.iter().any(|param| param.name == "self"))
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
        let type_part = &name[..pos];
        let method_part = &name[pos + 1..];
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
        let lower_joined = format!("{}_{}", type_part.to_lowercase(), method_part);
        if let Some(resolved) = use_map.get(&lower_joined).or_else(|| import_map.get(&lower_joined)) {
            return Some(resolved.clone());
        }
        if !method_part.is_empty() {
            if let Some(resolved) = use_map.get(method_part).or_else(|| import_map.get(method_part)) {
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
pub(crate) fn resolve_by_suffix(
    name: &str,
    suffix_index: &std::collections::HashMap<String, Vec<String>>,
) -> Option<String> {
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
pub(crate) fn build_import_map(
    file_sources: &[(PathBuf, String)],
    source_dirs: &[PathBuf],
    fallback_root: &Path,
) -> ImportMapResult {
    use std::collections::{HashMap, HashSet};

    let mut raw_to_mangled: HashMap<String, Vec<String>> = HashMap::new();
    let mut struct_defs: HashMap<String, Vec<(String, simple_parser::Type)>> = HashMap::new();
    let mut duplicate_struct_defs: HashMap<String, Vec<Vec<(String, simple_parser::Type)>>> = HashMap::new();
    let mut enum_defs: HashMap<String, Vec<(String, Option<Vec<simple_parser::Type>>)>> = HashMap::new();
    let mut duplicate_enum_defs: HashSet<String> = HashSet::new();
    let mut data_exports: HashSet<String> = HashSet::new();
    let mut fn_arities: HashMap<String, usize> = HashMap::new();
    let mut trait_impls: HashMap<String, Vec<String>> = HashMap::new();
    // Bare function name -> declared return type. This includes primitive
    // returns: losing `u64` here turns native comparisons into mixed ANY/scalar
    // operations whose tagged ABI differs from raw machine integers.
    let mut fn_return_types: HashMap<String, simple_parser::Type> = HashMap::new();

    let mut seen_canonical = HashSet::new();
    for (path, source) in file_sources {
        let canonical_path = safe_canonicalize(path);
        if !seen_canonical.insert(canonical_path) {
            continue;
        }
        let per_file_root = source_root_for_file(path, source_dirs, fallback_root);
        let prefix = module_prefix_from_path(path, &per_file_root);
        let filtered_source =
            crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(source, super::effective_target().arch);
        let mut parser = simple_parser::Parser::new(&filtered_source);
        if let Ok(mut ast) = parser.parse() {
            // Keep the arity/return-type map consistent with the codegen unit:
            // drop wrong-arch `@cfg` function variants so a non-target variant
            // does not seed these maps (bug
            // x64_freestanding_cfg_multivariant_misdispatch).
            super::discovery::strip_inactive_cfg_arch_fns(&mut ast, super::effective_target().arch);
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::Function(f) => {
                        if !f.body.statements.is_empty() {
                            let mangled = format!("{}__{}", prefix, f.name);
                            fn_arities.insert(mangled.clone(), f.params.len());
                            raw_to_mangled.entry(f.name.clone()).or_default().push(mangled);
                            // Preserve every declared return type. The lowerer
                            // discards types it cannot resolve, and the collision
                            // handling below removes ambiguous bare function names.
                            let captured = f.return_type.clone();
                            if let Some(cap) = captured {
                                match fn_return_types.entry(f.name.clone()) {
                                    std::collections::hash_map::Entry::Occupied(mut e) => {
                                        if e.get() != &cap {
                                            // Conflicting return types for the same bare
                                            // name: mark ambiguous (dropped before return).
                                            e.insert(simple_parser::Type::Simple(String::new()));
                                        }
                                    }
                                    std::collections::hash_map::Entry::Vacant(e) => {
                                        e.insert(cap);
                                    }
                                }
                            }
                        }
                    }
                    simple_parser::ast::Node::Class(c) => {
                        // Register the bare type name so cross-module imports of the
                        // class type resolve to the defining module's mangled symbol
                        // (e.g. "VfsManager" → "services__vfs__vfs__VfsManager").
                        // Without this, declare_globals falls back to mangle_name() which
                        // uses the *importing* file's prefix, producing wrong references.
                        let type_mangled = format!("{}__{}", prefix, c.name);
                        raw_to_mangled
                            .entry(c.name.clone())
                            .or_default()
                            .push(type_mangled.clone());
                        // Class type globals are data objects (type descriptors / vtable anchors),
                        // not function symbols — mark them so declare_globals uses the data path.
                        data_exports.insert(type_mangled);
                        if !c.fields.is_empty() {
                            let fields: Vec<(String, simple_parser::Type)> =
                                c.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
                            record_struct_fields(&mut struct_defs, &mut duplicate_struct_defs, &c.name, fields);
                        }
                        for m in &c.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", c.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, c.name, m.name));
                                fn_arities.insert(mangled.clone(), method_arity(m));
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
                            let arity = m.params.len()
                                + usize::from(!matches!(m.kind, simple_parser::ast::ExternMethodKind::Static));
                            fn_arities.insert(mangled.clone(), arity);
                            raw_to_mangled.entry(raw.clone()).or_default().push(mangled.clone());
                            raw_to_mangled.entry(m.name.clone()).or_default().push(mangled);
                        }
                    }
                    simple_parser::ast::Node::Let(l) => {
                        if let Some(name) = extract_let_name(&l.pattern) {
                            let mangled = format!("{}__{}", prefix, name);
                            raw_to_mangled.entry(name).or_default().push(mangled.clone());
                            // Module-level `var`/`val` (via `let`) is data, not a function.
                            data_exports.insert(mangled);
                        }
                    }
                    simple_parser::ast::Node::Const(c) => {
                        let mangled = format!("{}__{}", prefix, c.name);
                        raw_to_mangled.entry(c.name.clone()).or_default().push(mangled.clone());
                        // Module-level `const`/`val` is data, not a function.
                        data_exports.insert(mangled);
                    }
                    simple_parser::ast::Node::Static(s) => {
                        let mangled = format!("{}__{}", prefix, s.name);
                        raw_to_mangled.entry(s.name.clone()).or_default().push(mangled.clone());
                        // Module-level `static` is data, not a function.
                        data_exports.insert(mangled);
                    }
                    simple_parser::ast::Node::Struct(s) => {
                        // Register the bare struct type name so cross-module imports
                        // resolve to the defining module's symbol, not the importer's.
                        let type_mangled = format!("{}__{}", prefix, s.name);
                        raw_to_mangled
                            .entry(s.name.clone())
                            .or_default()
                            .push(type_mangled.clone());
                        data_exports.insert(type_mangled);
                        if !s.fields.is_empty() {
                            let fields: Vec<(String, simple_parser::Type)> =
                                s.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
                            record_struct_fields(&mut struct_defs, &mut duplicate_struct_defs, &s.name, fields);
                        }
                        for m in &s.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", s.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, s.name, m.name));
                                fn_arities.insert(mangled.clone(), method_arity(m));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                    }
                    simple_parser::ast::Node::Enum(e) => {
                        // Register the bare enum type name so cross-module imports
                        // resolve to the defining module's symbol, not the importer's.
                        let type_mangled = format!("{}__{}", prefix, e.name);
                        raw_to_mangled
                            .entry(e.name.clone())
                            .or_default()
                            .push(type_mangled.clone());
                        data_exports.insert(type_mangled);
                        // W15-H: harvest enum payload types into the global
                        // enum-defs sidecar so the lowerer can eagerly seed
                        // `module.types.name_to_id` and `self.globals` with
                        // the real enum TypeId for cross-module receivers.
                        let mut variant_summary: Vec<(String, Option<Vec<simple_parser::Type>>)> = e
                            .variants
                            .iter()
                            .map(|v| {
                                let payload = v
                                    .fields
                                    .as_ref()
                                    .map(|fields| fields.iter().map(|field| field.ty.clone()).collect());
                                (v.name.clone(), payload)
                            })
                            .collect();
                        if enum_defs.contains_key(&e.name) {
                            duplicate_enum_defs.insert(e.name.clone());
                        }
                        let entry = enum_defs.entry(e.name.clone()).or_default();
                        if duplicate_enum_defs.contains(&e.name) {
                            let erase_payload = |payload: &mut Option<Vec<simple_parser::Type>>| {
                                if let Some(fields) = payload {
                                    for field in fields {
                                        *field = simple_parser::Type::Simple("Any".to_string());
                                    }
                                }
                            };
                            for (_, payload) in entry.iter_mut() {
                                erase_payload(payload);
                            }
                            for (_, payload) in variant_summary.iter_mut() {
                                erase_payload(payload);
                            }
                        }
                        for (variant_name, variant_payload) in variant_summary {
                            if let Some((_, existing_payload)) =
                                entry.iter_mut().find(|(name, _)| name == &variant_name)
                            {
                                let conflicting_payload_len = match (&*existing_payload, &variant_payload) {
                                    (None, None) => None,
                                    (Some(left), Some(right)) => Some(left.len().max(right.len())),
                                    (Some(fields), None) | (None, Some(fields)) => Some(fields.len().max(1)),
                                };
                                if let Some(len) = conflicting_payload_len {
                                    *existing_payload = Some(vec![simple_parser::Type::Simple("Any".to_string()); len]);
                                }
                            } else {
                                entry.push((variant_name, variant_payload));
                            }
                        }
                        for m in &e.methods {
                            if !m.body.statements.is_empty() {
                                let raw = format!("{}.{}", e.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, e.name, m.name));
                                fn_arities.insert(mangled.clone(), method_arity(m));
                                raw_to_mangled.entry(m.name.clone()).or_default().push(mangled.clone());
                                raw_to_mangled.entry(raw).or_default().push(mangled);
                            }
                        }
                        for v in &e.variants {
                            if let Some(ref fields) = v.fields {
                                let named: Vec<(String, simple_parser::Type)> = fields
                                    .iter()
                                    .filter_map(|f| f.name.as_ref().map(|n| (n.clone(), f.ty.clone())))
                                    .collect();
                                if !named.is_empty() {
                                    record_struct_fields(&mut struct_defs, &mut duplicate_struct_defs, &v.name, named);
                                }
                            }
                        }
                    }
                    simple_parser::ast::Node::Trait(t) => {
                        for m in &t.methods {
                            if has_concrete_body(&m.body) {
                                let raw = format!("{}.{}", t.name, m.name);
                                let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, t.name, m.name));
                                fn_arities.insert(mangled.clone(), method_arity(m));
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
                            if let Some(trait_name) = &imp.trait_name {
                                let implementations = trait_impls.entry(trait_name.clone()).or_default();
                                if !implementations.iter().any(|candidate| candidate == type_name) {
                                    implementations.push(type_name.to_string());
                                }
                            }
                            for m in &imp.methods {
                                if !m.body.statements.is_empty() {
                                    let raw = format!("{}.{}", type_name, m.name);
                                    let mangled = sanitize_mangled(format!("{}__{}.{}", prefix, type_name, m.name));
                                    fn_arities.insert(mangled.clone(), method_arity(m));
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
                                fn_arities.insert(mangled.clone(), method_arity(m));
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

    // Build a deterministic re-export index. Package `__init__.spl` facades
    // use their parent directory as the public module key and select an exact
    // sibling owner; candidate order is never a resolution rule.
    #[derive(Default)]
    struct ExportMetadata {
        path: PathBuf,
        root: PathBuf,
        prefix: String,
        public_imports: Vec<(Vec<String>, simple_parser::ast::ImportTarget, bool)>,
        explicit_targets: Vec<simple_parser::ast::ImportTarget>,
        bare_exports: Vec<String>,
    }

    let mut metadata = Vec::new();
    let mut seen_canonical_reexport = std::collections::HashSet::new();
    for (path, source) in file_sources {
        let canonical_path = safe_canonicalize(path);
        if !seen_canonical_reexport.insert(canonical_path.clone()) {
            continue;
        }
        let per_file_root = source_root_for_file(path, source_dirs, fallback_root);
        let prefix = module_prefix_from_path(path, &per_file_root);
        let filtered_source =
            crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(source, super::effective_target().arch);
        let mut parser = simple_parser::Parser::new(&filtered_source);
        if let Ok(mut ast) = parser.parse() {
            super::discovery::strip_inactive_cfg_arch_fns(&mut ast, super::effective_target().arch);
            let mut item_metadata = ExportMetadata {
                path: canonical_path,
                root: per_file_root,
                prefix,
                ..Default::default()
            };
            let mut internal_imports = Vec::new();
            for item in &ast.items {
                match item {
                    simple_parser::ast::Node::UseStmt(u) => {
                        internal_imports.push((u.path.segments.clone(), u.target.clone()));
                    }
                    simple_parser::ast::Node::MultiUse(mu) => {
                        for (path, target) in &mu.imports {
                            internal_imports.push((path.segments.clone(), target.clone()));
                        }
                    }
                    simple_parser::ast::Node::ExportUseStmt(export) => {
                        if export.path.segments.is_empty() {
                            collect_target_names(&export.target, &mut item_metadata.bare_exports);
                        } else {
                            item_metadata.public_imports.push((
                                export.path.segments.clone(),
                                export.target.clone(),
                                false,
                            ));
                            item_metadata.explicit_targets.push(export.target.clone());
                        }
                    }
                    _ => {}
                }
            }
            item_metadata.bare_exports.sort();
            item_metadata.bare_exports.dedup();
            for (segments, target) in internal_imports {
                if item_metadata
                    .bare_exports
                    .iter()
                    .any(|name| import_target_exports_name(&target, name))
                    || matches!(target, simple_parser::ast::ImportTarget::Glob)
                        && !item_metadata.bare_exports.is_empty()
                {
                    item_metadata.public_imports.push((segments, target, true));
                }
            }
            metadata.push(item_metadata);
        }
    }
    metadata.sort_by(|a, b| a.path.cmp(&b.path));

    let mut owner_sets = std::collections::BTreeMap::new();
    for _ in 0..=metadata.len() {
        let mut changed = false;
        for item in &metadata {
            for (segments, target, bare_only) in &item.public_imports {
                let norm_segments: Vec<&str> = segments
                    .iter()
                    .map(|s| if s == "std" { "lib" } else { s.as_str() })
                    .collect();
                let mut bindings = Vec::new();
                collect_target_bindings(target, &mut bindings);
                if matches!(target, simple_parser::ast::ImportTarget::Glob) {
                    let names: Vec<String> = if *bare_only {
                        item.bare_exports.clone()
                    } else {
                        raw_to_mangled.keys().cloned().collect()
                    };
                    bindings.extend(names.into_iter().map(|name| (name.clone(), name)));
                }
                for (public_name, source_name) in bindings {
                    if *bare_only && !item.bare_exports.contains(&public_name) {
                        continue;
                    }
                    let owners =
                        resolve_import_owner_candidates(&source_name, &norm_segments, &raw_to_mangled, &owner_sets);
                    let entry = owner_sets
                        .entry((item.prefix.clone(), public_name))
                        .or_insert_with(std::collections::BTreeSet::new);
                    let before = entry.len();
                    entry.extend(owners);
                    changed |= entry.len() != before;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut package_owner_sets = std::collections::BTreeMap::new();
    for item in metadata
        .iter()
        .filter(|item| item.path.file_name().is_some_and(|name| name == "__init__.spl"))
    {
        let Some(parent) = item.path.parent() else { continue };
        let package_prefix = module_prefix_from_path(parent, &item.root);
        for name in &item.bare_exports {
            let mut explicit = std::collections::BTreeSet::new();
            let mut implicit = std::collections::BTreeSet::new();
            for sibling in metadata.iter().filter(|candidate| {
                candidate.path.parent() == Some(parent)
                    && candidate.path.file_name().is_some_and(|file| file != "__init__.spl")
            }) {
                let expected = sanitize_mangled(format!("{}__{}", sibling.prefix, name));
                if raw_to_mangled
                    .get(name)
                    .is_some_and(|candidates| candidates.iter().any(|candidate| candidate == &expected))
                {
                    if sibling.bare_exports.contains(name) {
                        explicit.insert(expected);
                    } else {
                        implicit.insert(expected);
                    }
                }
                if let Some(owners) = owner_sets.get(&(sibling.prefix.clone(), name.clone())) {
                    if sibling.bare_exports.contains(name)
                        || sibling
                            .explicit_targets
                            .iter()
                            .any(|target| import_target_exports_name(target, name))
                    {
                        explicit.extend(owners.iter().cloned());
                    }
                }
            }
            package_owner_sets.insert(
                (package_prefix.clone(), name.clone()),
                if explicit.is_empty() { implicit } else { explicit },
            );
        }
    }

    let mut re_exports: std::collections::HashMap<String, std::collections::HashMap<String, String>> =
        std::collections::HashMap::new();
    for ((prefix, name), owners) in owner_sets.into_iter().chain(package_owner_sets) {
        if owners.len() == 1 {
            re_exports
                .entry(prefix)
                .or_default()
                .insert(name, owners.into_iter().next().unwrap());
        }
    }

    // Hardcode critical logging symbols
    let logger_debug = sanitize_mangled("compiler__common__config__Logger.debug".to_string());
    map.entry("Logger.debug".to_string())
        .or_insert_with(|| logger_debug.clone());
    map.entry("debug".to_string()).or_insert_with(|| logger_debug.clone());

    let logger_trace = sanitize_mangled("compiler__common__config__Logger.trace".to_string());
    map.entry("Logger.trace".to_string())
        .or_insert_with(|| logger_trace.clone());
    map.entry("trace".to_string()).or_insert_with(|| logger_trace.clone());

    let boot_debug = sanitize_mangled("compiler__driver__driver_types__BootLogger.debug".to_string());
    map.entry("BootLogger.debug".to_string())
        .or_insert_with(|| boot_debug.clone());

    let boot_trace = sanitize_mangled("compiler__driver__driver_types__BootLogger.trace".to_string());
    map.entry("BootLogger.trace".to_string())
        .or_insert_with(|| boot_trace.clone());

    let driver_compile = sanitize_mangled("compiler__driver__driver__CompilerDriver.compile".to_string());
    map.entry("CompilerDriver.compile".to_string())
        .or_insert_with(|| driver_compile.clone());

    let compile_result_get_errors =
        sanitize_mangled("compiler__driver__driver_types__CompileResult.get_errors".to_string());
    map.entry("CompileResult.get_errors".to_string())
        .or_insert_with(|| compile_result_get_errors.clone());
    map.entry("get_errors".to_string())
        .or_insert_with(|| compile_result_get_errors.clone());

    // A bare payload owner that has multiple definitions is not safe to
    // resolve through the global name table. Erase the whole field, including
    // nested wrappers, so discovery order cannot invent an owner.
    let mut ambiguous_type_owners = duplicate_enum_defs;
    ambiguous_type_owners.extend(duplicate_struct_defs.keys().cloned());
    for variants in enum_defs.values_mut() {
        for (_, payload) in variants {
            if let Some(fields) = payload {
                for field in fields {
                    if type_mentions_ambiguous_owner(field, &ambiguous_type_owners) {
                        *field = simple_parser::Type::Simple("Any".to_string());
                    }
                }
            }
        }
    }

    // Drop ambiguous (empty-name sentinel) entries before returning.
    fn_return_types.retain(|_, ty| !matches!(ty, simple_parser::Type::Simple(s) if s.is_empty()));
    ImportMapResult {
        map,
        ambiguous,
        all_mangled: raw_to_mangled,
        re_exports,
        trait_impls,
        struct_defs,
        duplicate_struct_defs,
        enum_defs,
        data_exports,
        fn_arities,
        fn_return_types,
    }
}

fn type_mentions_ambiguous_owner(ty: &simple_parser::Type, ambiguous: &std::collections::HashSet<String>) -> bool {
    use simple_parser::Type;

    match ty {
        Type::Simple(name) | Type::DynTrait(name) | Type::UnitWithRepr { name, .. } => ambiguous.contains(name),
        Type::Generic { name, args } => {
            ambiguous.contains(name) || args.iter().any(|arg| type_mentions_ambiguous_owner(arg, ambiguous))
        }
        Type::Capability { inner, .. }
        | Type::Pointer { inner, .. }
        | Type::Optional(inner)
        | Type::Array { element: inner, .. }
        | Type::Simd { element: inner, .. } => type_mentions_ambiguous_owner(inner, ambiguous),
        Type::Tuple(fields) | Type::Union(fields) => fields
            .iter()
            .any(|field| type_mentions_ambiguous_owner(field, ambiguous)),
        Type::LabeledTuple(fields) => fields
            .iter()
            .any(|field| type_mentions_ambiguous_owner(&field.ty, ambiguous)),
        Type::Function { params, ret } => {
            params
                .iter()
                .any(|param| type_mentions_ambiguous_owner(param, ambiguous))
                || ret
                    .as_deref()
                    .is_some_and(|ret| type_mentions_ambiguous_owner(ret, ambiguous))
        }
        Type::Constructor { target, args } => {
            type_mentions_ambiguous_owner(target, ambiguous)
                || args
                    .as_ref()
                    .is_some_and(|args| args.iter().any(|arg| type_mentions_ambiguous_owner(arg, ambiguous)))
        }
        Type::TypeBinding { value, .. } => type_mentions_ambiguous_owner(value, ambiguous),
        Type::SelfType | Type::ConstKeySet { .. } | Type::DependentKeys { .. } => false,
    }
}

fn record_struct_fields(
    struct_defs: &mut std::collections::HashMap<String, Vec<(String, simple_parser::Type)>>,
    duplicate_struct_defs: &mut std::collections::HashMap<String, Vec<Vec<(String, simple_parser::Type)>>>,
    name: &str,
    fields: Vec<(String, simple_parser::Type)>,
) {
    if fields.is_empty() {
        return;
    }

    match struct_defs.get(name) {
        None => {
            struct_defs.insert(name.to_string(), fields);
        }
        Some(existing) if *existing == fields => {}
        Some(existing) => {
            let variants = duplicate_struct_defs
                .entry(name.to_string())
                .or_insert_with(|| vec![existing.clone()]);
            if !variants.iter().any(|candidate| candidate == &fields) {
                variants.push(fields);
            }
        }
    }
}

/// Build a per-module use map from AST `use` statements.
pub(crate) fn build_use_map_from_ast(
    ast: &simple_parser::ast::Module,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> std::collections::HashMap<String, String> {
    let mut use_map = std::collections::HashMap::new();

    super::discovery::visit_ast_nodes(&ast.items, &mut |item| match item {
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
    });

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
            // Also resolve bare function names that belong to this module.
            // When a module exports free functions (e.g. `use std.common.ctype` imports
            // `is_digit`), the bare name "is_digit" is NOT keyed as "ctype.is_digit" in
            // all_mangled, so the prefix loop above misses it.  Walk all bare (non-dotted)
            // names and use resolve_import_name_strict with the current use-path segments
            // to find ones that uniquely belong to this module.
            for (raw_name, candidates) in all_mangled.iter() {
                // Skip dotted names (already handled above) and names already resolved.
                if raw_name.contains('.') || use_map.contains_key(raw_name) {
                    continue;
                }
                // Only act when there are multiple candidates — single-candidate names
                // are already unambiguous and don't need the module-scoped override.
                if candidates.len() <= 1 {
                    continue;
                }
                if let Some(mangled) = resolve_import_name_strict(raw_name, &segments, all_mangled, re_exports) {
                    use_map.insert(raw_name.clone(), mangled);
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
        simple_parser::ast::ImportTarget::Glob => {
            for raw_name in all_mangled.keys() {
                if let Some(mangled) = resolve_import_name_strict(raw_name, &segments, all_mangled, re_exports) {
                    use_map.insert(raw_name.clone(), mangled);
                }
            }
        }
    }
}

fn resolve_import_name(
    func_name: &str,
    use_segments: &[&str],
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> Option<String> {
    if let Some(resolved) = resolve_import_name_strict(func_name, use_segments, all_mangled, re_exports) {
        return Some(resolved);
    }

    let candidates = all_mangled.get(func_name)?;
    (candidates.len() == 1).then(|| candidates[0].clone())
}

fn resolve_import_name_strict(
    func_name: &str,
    use_segments: &[&str],
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    re_exports: &std::collections::HashMap<String, std::collections::HashMap<String, String>>,
) -> Option<String> {
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

    let candidates = all_mangled.get(func_name)?;
    let matching: Vec<&String> = candidates
        .iter()
        .filter(|candidate| mangled_matches_use_path(candidate, use_segments))
        .collect();
    if matching.len() == 1 {
        return Some(matching[0].clone());
    }

    None
}

fn collect_target_names(target: &simple_parser::ast::ImportTarget, names: &mut Vec<String>) {
    match target {
        simple_parser::ast::ImportTarget::Single(name) => names.push(name.clone()),
        simple_parser::ast::ImportTarget::Aliased { alias, .. } => names.push(alias.clone()),
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                collect_target_names(item, names);
            }
        }
        simple_parser::ast::ImportTarget::Glob => {}
    }
}

fn collect_target_bindings(target: &simple_parser::ast::ImportTarget, bindings: &mut Vec<(String, String)>) {
    match target {
        simple_parser::ast::ImportTarget::Single(name) => bindings.push((name.clone(), name.clone())),
        simple_parser::ast::ImportTarget::Aliased { name, alias } => {
            bindings.push((alias.clone(), name.clone()));
        }
        simple_parser::ast::ImportTarget::Group(items) => {
            for item in items {
                collect_target_bindings(item, bindings);
            }
        }
        simple_parser::ast::ImportTarget::Glob => {}
    }
}

fn import_target_exports_name(target: &simple_parser::ast::ImportTarget, wanted: &str) -> bool {
    match target {
        simple_parser::ast::ImportTarget::Single(name) => name == wanted,
        simple_parser::ast::ImportTarget::Aliased { alias, .. } => alias == wanted,
        simple_parser::ast::ImportTarget::Group(items) => {
            items.iter().any(|item| import_target_exports_name(item, wanted))
        }
        simple_parser::ast::ImportTarget::Glob => true,
    }
}

fn resolve_import_owner_candidates(
    func_name: &str,
    use_segments: &[&str],
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    owner_sets: &std::collections::BTreeMap<(String, String), std::collections::BTreeSet<String>>,
) -> std::collections::BTreeSet<String> {
    let mut owners = std::collections::BTreeSet::new();
    let expected_prefix = use_segments.join("__");
    if let Some(forwarded) = owner_sets.get(&(expected_prefix, func_name.to_string())) {
        owners.extend(forwarded.iter().cloned());
    }
    if use_segments.len() > 1 {
        let stripped_prefix = use_segments[1..].join("__");
        if let Some(forwarded) = owner_sets.get(&(stripped_prefix, func_name.to_string())) {
            owners.extend(forwarded.iter().cloned());
        }
    }
    if let Some(candidates) = all_mangled.get(func_name) {
        owners.extend(
            candidates
                .iter()
                .filter(|candidate| mangled_matches_use_path(candidate, use_segments))
                .cloned(),
        );
    }
    owners
}

fn mangled_matches_use_path(mangled: &str, use_segments: &[&str]) -> bool {
    let normalized = mangled.replace("_dot_", "__").replace('.', "__");
    let parts: Vec<&str> = normalized.split("__").collect();
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
