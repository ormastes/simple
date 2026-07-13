//! File discovery: full-scan and entry-closure based .spl file discovery,
//! reachable module path extraction, file deduplication.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

use simple_common::target::TargetArch;

use super::{
    collect_spl_files_recursive, native_project_rust_trace_enabled, safe_canonicalize, same_file_path,
    NativeProjectBuilder,
};

// `@cfg(<arch>)` evaluation + function-variant stripping now live in the
// shared `pipeline::cfg_strip` module so the `bin/simple run` JIT/interpreter
// paths apply the same filter as native-project builds (bug
// `x64_freestanding_cfg_multivariant_misdispatch`). Re-exported here for the
// existing native_project call sites (compiler.rs, imports.rs, tests.rs).
pub(crate) use crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns;
use crate::pipeline::cfg_strip::cfg_name_to_arch;

/// Extract the arch-gating verdict for a `.spl` source, if its first
/// meaningful line is a whole-file `@cfg(<arch>)` (optionally
/// `@cfg(not(<arch>))`) decorator.
///
/// Returns `Some(true)` if the file should be included for `target_arch`,
/// `Some(false)` if it should be excluded, and `None` if the file has no
/// leading arch cfg gate (not `@cfg`-decorated at all, or gated on a
/// non-arch condition) -- callers should treat `None` as "always include",
/// matching today's behavior for every file that isn't gated this way.
///
/// This intentionally only recognizes a single leading `@cfg(...)` line, not
/// the full per-declaration preprocessor grammar (multi-line brace tracking,
/// nested conditions, etc.) -- that full evaluation already exists in
/// `parser_preprocessor.spl` and is out of scope to reimplement here. The
/// narrower goal is just to stop native-project discovery from being
/// completely blind to the common "this whole file is one arch's HAL
/// implementation" pattern documented in `src/os/kernel/arch/hal.spl`.
pub(crate) fn file_arch_cfg_gate(source: &str, target_arch: TargetArch) -> Option<bool> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if !trimmed.starts_with("@cfg(") {
            return None;
        }
        let inner = trimmed.strip_prefix("@cfg(")?.trim_end();
        let inner = inner.strip_suffix(')').unwrap_or(inner);
        // Skip `"key", "value"` style conditions (e.g. @cfg("target_arch", "arm")) --
        // not a bare arch alias, leave ungated.
        if inner.contains(',') || inner.contains('"') {
            return None;
        }
        let (negate, name) = match inner.strip_prefix("not(") {
            Some(rest) => (true, rest.trim_end_matches(')').trim()),
            None => (false, inner.trim()),
        };
        return cfg_name_to_arch(name).map(|arch| {
            let matches = arch == target_arch;
            if negate {
                !matches
            } else {
                matches
            }
        });
    }
    None
}

fn import_target_names(target: &simple_parser::ast::ImportTarget, names: &mut Vec<String>) {
    use simple_parser::ast::ImportTarget;
    match target {
        ImportTarget::Single(name) => names.push(name.clone()),
        ImportTarget::Aliased { alias, .. } => names.push(alias.clone()),
        ImportTarget::Group(items) => {
            for item in items {
                import_target_names(item, names);
            }
        }
        ImportTarget::Glob => {}
    }
}

fn import_target_has_glob(target: &simple_parser::ast::ImportTarget) -> bool {
    match target {
        simple_parser::ast::ImportTarget::Group(items) => items.iter().any(import_target_has_glob),
        simple_parser::ast::ImportTarget::Glob => true,
        _ => false,
    }
}

fn bare_export_names(items: &[simple_parser::ast::Node]) -> Vec<String> {
    let mut names = Vec::new();
    for item in items {
        if let simple_parser::ast::Node::ExportUseStmt(export) = item {
            if export.path.segments.is_empty() {
                import_target_names(&export.target, &mut names);
            }
        }
    }
    names.sort();
    names.dedup();
    names
}

fn provided_export_names(items: &[simple_parser::ast::Node], requested: &[String]) -> (Vec<String>, Vec<String>, bool) {
    use simple_parser::ast::{Node, Pattern};

    let mut defined = Vec::new();
    let mut imported = Vec::new();
    let mut forwarded = Vec::new();
    let mut imports_all = false;
    let mut forwards_glob = false;
    let bare_exports = bare_export_names(items);
    for item in items {
        match item {
            Node::Function(def) if !def.body.statements.is_empty() => defined.push(def.name.clone()),
            Node::Extern(def) => defined.push(def.name.clone()),
            Node::Class(def) => defined.push(def.name.clone()),
            Node::Struct(def) => defined.push(def.name.clone()),
            Node::Enum(def) => defined.push(def.name.clone()),
            Node::Trait(def) => defined.push(def.name.clone()),
            Node::Let(stmt) => match &stmt.pattern {
                Pattern::Identifier(name) | Pattern::MutIdentifier(name) => defined.push(name.clone()),
                _ => {}
            },
            Node::Const(stmt) => defined.push(stmt.name.clone()),
            Node::Static(stmt) => defined.push(stmt.name.clone()),
            Node::UseStmt(stmt) => {
                imports_all |= import_target_has_glob(&stmt.target);
                import_target_names(&stmt.target, &mut imported);
            }
            Node::MultiUse(stmt) => {
                for (_, target) in &stmt.imports {
                    imports_all |= import_target_has_glob(target);
                    import_target_names(target, &mut imported);
                }
            }
            Node::ExportUseStmt(stmt) if !stmt.path.segments.is_empty() => {
                imports_all |= import_target_has_glob(&stmt.target);
                forwards_glob |= import_target_has_glob(&stmt.target);
                import_target_names(&stmt.target, &mut imported);
                import_target_names(&stmt.target, &mut forwarded);
            }
            _ => {}
        }
    }

    let mut explicit: Vec<String> = requested
        .iter()
        .filter(|name| {
            forwarded.contains(name)
                || (bare_exports.contains(name) && (defined.contains(name) || imports_all || imported.contains(name)))
        })
        .cloned()
        .collect();
    explicit.sort();
    explicit.dedup();
    let mut implicit: Vec<String> = requested
        .iter()
        .filter(|name| defined.contains(name))
        .cloned()
        .collect();
    implicit.sort();
    implicit.dedup();
    (explicit, implicit, forwards_glob)
}

impl NativeProjectBuilder {
    /// Discover all .spl files in source directories.
    /// Returns ALL paths including symlink aliases (needed for import map indexing).
    /// Use `deduplicate_for_compilation` to get the unique set for actual compilation.
    pub(crate) fn discover_files(&self) -> Result<Vec<PathBuf>, String> {
        if self.config.entry_closure {
            if let Some(entry_file) = &self.entry_file {
                return self.discover_reachable_files(entry_file);
            }
            return Err("entry-closure requires --entry".to_string());
        }
        Ok(self.discover_files_full_scan())
    }

    fn discover_files_full_scan(&self) -> Vec<PathBuf> {
        let mut files = Vec::new();
        for dir in &self.source_dirs {
            if dir.is_dir() {
                collect_spl_files_recursive(dir, &mut files);
            }
        }
        if let Some(entry_file) = &self.entry_file {
            let canonical_entry = safe_canonicalize(entry_file);
            if !files.iter().any(|path| same_file_path(path, &canonical_entry)) {
                files.push(entry_file.clone());
            }
        }
        files.sort();

        // Drop files whose leading `@cfg(<arch>)` gate does not match the
        // build's effective target arch (see `file_arch_cfg_gate`). Full-scan
        // discovery previously ignored `@cfg` entirely, so a cross-arch build
        // (e.g. --target x86_64 over a source tree containing riscv64-only
        // HAL files) could pull wrong-arch files into compilation and, via
        // `collected_inline_asm_blocks()`, wrong-arch inline asm into the
        // link (see src/os/kernel/arch/hal.spl header). The entry file is
        // always kept regardless of its own gate, matching entry-closure's
        // unconditional inclusion of the requested entry point.
        let target_arch = super::effective_target().arch;
        let canonical_entry = self.entry_file.as_ref().map(|p| safe_canonicalize(p));
        files.retain(|path| {
            if let Some(entry) = &canonical_entry {
                if same_file_path(path, entry) {
                    return true;
                }
            }
            let source = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(_) => return true,
            };
            file_arch_cfg_gate(&source, target_arch).unwrap_or(true)
        });
        files
    }

    fn discover_reachable_files(&self, entry_file: &Path) -> Result<Vec<PathBuf>, String> {
        self.discover_reachable_files_with_sources(entry_file)
            .map(|files| files.into_iter().map(|(path, _)| path).collect())
    }

    /// Discover reachable files and retain their source text so the build
    /// phase can reuse the already-read contents.
    pub(crate) fn discover_reachable_files_with_sources(
        &self,
        entry_file: &Path,
    ) -> Result<Vec<(PathBuf, String)>, String> {
        let canonical_entry = safe_canonicalize(entry_file);
        let rust_trace = native_project_rust_trace_enabled();
        if rust_trace {
            eprintln!(
                "[native-rust-trace] entry-closure discovery start entry={}",
                canonical_entry.display()
            );
        }

        // Build one resolver per source dir so imports can cross source boundaries.
        let mut resolvers: Vec<crate::module_resolver::ModuleResolver> = self
            .source_dirs
            .iter()
            .map(|dir| {
                let canonical_dir = safe_canonicalize(dir);
                crate::module_resolver::ModuleResolver::new(self.project_root.clone(), canonical_dir)
            })
            .collect();
        let project_src = self.project_root.join("src");
        if project_src.is_dir() {
            let canonical_project_src = safe_canonicalize(&project_src);
            if !self
                .source_dirs
                .iter()
                .any(|dir| safe_canonicalize(dir) == canonical_project_src)
            {
                resolvers.push(crate::module_resolver::ModuleResolver::new(
                    self.project_root.clone(),
                    canonical_project_src,
                ));
            }
        }

        // Ensure at least the effective root for the entry file is covered.
        if resolvers.is_empty() {
            let resolver_root = self.effective_source_root_for(&canonical_entry);
            resolvers.push(crate::module_resolver::ModuleResolver::new(
                self.project_root.clone(),
                resolver_root,
            ));
        }

        // Canonicalize source dirs once for the filesystem fallback.
        let mut canonical_source_dirs: Vec<PathBuf> = self.source_dirs.iter().map(|d| safe_canonicalize(d)).collect();
        if project_src.is_dir() {
            let canonical_project_src = safe_canonicalize(&project_src);
            if !canonical_source_dirs.contains(&canonical_project_src) {
                canonical_source_dirs.push(canonical_project_src);
            }
        }

        let mut queue = VecDeque::from([canonical_entry.clone()]);
        let mut queued = HashSet::from([canonical_entry.clone()]);
        let mut seen = HashSet::new();
        let mut files: Vec<(PathBuf, String)> = Vec::new();

        while let Some(path) = queue.pop_front() {
            let canonical = safe_canonicalize(&path);
            if !seen.insert(canonical.clone()) {
                continue;
            }
            if rust_trace {
                eprintln!("[native-rust-trace] discover visit {}", canonical.display());
            }

            if canonical.extension().is_some_and(|e| e == "smf") {
                continue;
            }

            let mut source = std::fs::read_to_string(&canonical)
                .map_err(|e| format!("failed to read {}: {}", canonical.display(), e))?;
            if source.contains('\r') {
                source = source.replace('\r', "");
            }

            let mut parser = simple_parser::Parser::new(&source);
            let mut module = parser.parse().map_err(|e| {
                let location = e
                    .span()
                    .map(|span| format!(" at {}:{}", span.line, span.column))
                    .unwrap_or_default();
                format!(
                    "failed to parse {}{} during discovery: {}",
                    canonical.display(),
                    location,
                    e
                )
            })?;
            let target_arch = super::effective_target().arch;
            strip_inactive_cfg_arch_fns(&mut module, target_arch);
            let mut found_deps: HashSet<PathBuf> = HashSet::new();

            // A package facade may export names implemented by sibling files.
            // Select those providers from cfg-stripped ASTs, never from text or
            // directory order, and reject ambiguous package ownership.
            if canonical.file_name().is_some_and(|name| name == "__init__.spl") {
                if module.items.iter().any(|item| {
                    matches!(item, simple_parser::ast::Node::ExportUseStmt(export)
                        if export.path.segments.is_empty() && import_target_has_glob(&export.target))
                }) {
                    return Err(format!(
                        "bare package `export *` is unsupported during native entry-closure discovery: {}",
                        canonical.display()
                    ));
                }
                let requested = bare_export_names(&module.items);
                if !requested.is_empty() {
                    let parent = canonical
                        .parent()
                        .ok_or_else(|| format!("package init has no parent: {}", canonical.display()))?;
                    let mut siblings: Vec<PathBuf> = std::fs::read_dir(parent)
                        .map_err(|e| format!("failed to read package {}: {}", parent.display(), e))?
                        .filter_map(Result::ok)
                        .map(|entry| entry.path())
                        .filter(|path| {
                            path.extension().is_some_and(|ext| ext == "spl")
                                && path
                                    .file_name()
                                    .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                        })
                        .map(|path| safe_canonicalize(&path))
                        .collect();
                    siblings.sort();
                    siblings.dedup();

                    let mut explicit_providers: BTreeMap<String, Vec<PathBuf>> =
                        requested.iter().cloned().map(|name| (name, Vec::new())).collect();
                    let mut implicit_providers = explicit_providers.clone();
                    let mut glob_forwarders = Vec::new();
                    for sibling in siblings {
                        let mut sibling_source = match std::fs::read_to_string(&sibling) {
                            Ok(source) => source,
                            Err(_) => continue,
                        };
                        if sibling_source.contains('\r') {
                            sibling_source = sibling_source.replace('\r', "");
                        }
                        if file_arch_cfg_gate(&sibling_source, target_arch) == Some(false) {
                            continue;
                        }
                        let mut sibling_parser = simple_parser::Parser::new(&sibling_source);
                        let mut sibling_module = match sibling_parser.parse() {
                            Ok(module) => module,
                            Err(_) => continue,
                        };
                        strip_inactive_cfg_arch_fns(&mut sibling_module, target_arch);
                        let (explicit, implicit, forwards_glob) =
                            provided_export_names(&sibling_module.items, &requested);
                        if forwards_glob {
                            glob_forwarders.push(sibling.clone());
                        }
                        for name in explicit {
                            explicit_providers.entry(name).or_default().push(sibling.clone());
                        }
                        for name in implicit {
                            implicit_providers.entry(name).or_default().push(sibling.clone());
                        }
                    }
                    found_deps.extend(glob_forwarders);
                    for name in requested {
                        let explicit = explicit_providers.remove(&name).unwrap_or_default();
                        let implicit = implicit_providers.remove(&name).unwrap_or_default();
                        let owners = if explicit.is_empty() { implicit } else { explicit };
                        match owners.as_slice() {
                            [owner] => {
                                found_deps.insert(owner.clone());
                            }
                            [] => {}
                            _ => {
                                return Err(format!(
                                    "ambiguous package export `{}` in {}: {}",
                                    name,
                                    canonical.display(),
                                    owners
                                        .iter()
                                        .map(|path| path.display().to_string())
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                ));
                            }
                        }
                    }
                }
            }

            // Try each resolver -- the first hit wins for each dependency.
            for resolver in &mut resolvers {
                for dep in extract_reachable_module_paths(&module, &canonical, resolver) {
                    let dep_canonical = safe_canonicalize(&dep);
                    found_deps.insert(dep_canonical);
                }
            }
            if rust_trace && !found_deps.is_empty() {
                eprintln!(
                    "[native-rust-trace] discover deps {} count={}",
                    canonical.display(),
                    found_deps.len()
                );
                for dep in found_deps.iter().take(8) {
                    eprintln!("  dep={}", dep.display());
                }
                if found_deps.len() > 8 {
                    eprintln!("  dep_more={}", found_deps.len() - 8);
                }
            }

            // Filesystem fallback: for any `use` statement whose segments form a
            // plausible path under one of the --source dirs, check the filesystem
            // directly.
            {
                use simple_parser::ast::{
                    AutoImportStmt, CommonUseStmt, ExportUseStmt, ImportTarget, ModDecl, ModulePath, MultiUse, Node,
                    UseStmt,
                };

                fn segments_from_use(path: &ModulePath, target: Option<&ImportTarget>) -> Vec<Vec<String>> {
                    let mut results = Vec::new();
                    if let Some(ImportTarget::Single(name)) | Some(ImportTarget::Aliased { name, .. }) = target {
                        let mut segs = path.segments.clone();
                        segs.push(name.clone());
                        results.push(segs);
                    }
                    results.push(path.segments.clone());
                    results
                }

                let mut use_segment_lists: Vec<Vec<String>> = Vec::new();
                for item in &module.items {
                    match item {
                        Node::UseStmt(UseStmt { path, target, .. }) => {
                            use_segment_lists.extend(segments_from_use(path, Some(target)));
                        }
                        Node::CommonUseStmt(CommonUseStmt { path, target, .. }) => {
                            use_segment_lists.extend(segments_from_use(path, Some(target)));
                        }
                        Node::ExportUseStmt(ExportUseStmt { path, target, .. }) => {
                            use_segment_lists.extend(segments_from_use(path, Some(target)));
                        }
                        Node::MultiUse(MultiUse { imports, .. }) => {
                            for (path, target) in imports {
                                use_segment_lists.extend(segments_from_use(path, Some(target)));
                            }
                        }
                        Node::AutoImportStmt(AutoImportStmt { path, .. }) => {
                            use_segment_lists.extend(segments_from_use(path, None));
                        }
                        Node::ModDecl(ModDecl { name, body, .. }) if body.is_none() => {
                            use_segment_lists.push(vec![name.clone()]);
                        }
                        _ => {}
                    }
                }

                for segments in &use_segment_lists {
                    if segments.is_empty() {
                        continue;
                    }
                    for src_dir in &canonical_source_dirs {
                        let dir_name = src_dir.file_name().and_then(|n| n.to_str()).unwrap_or("");

                        let try_segments: Vec<&[String]> = if !segments.is_empty() && segments[0] == dir_name {
                            vec![&segments[1..], &segments[..]]
                        } else {
                            vec![&segments[..]]
                        };

                        for segs in &try_segments {
                            if segs.is_empty() {
                                continue;
                            }
                            let rel_path: PathBuf = segs.iter().collect();
                            let spl_path = src_dir.join(&rel_path).with_extension("spl");
                            if spl_path.is_file() {
                                let dep_canonical = safe_canonicalize(&spl_path);
                                found_deps.insert(dep_canonical);
                                break;
                            }
                            let mod_path = src_dir.join(&rel_path).join("mod.spl");
                            if mod_path.is_file() {
                                let dep_canonical = safe_canonicalize(&mod_path);
                                found_deps.insert(dep_canonical);
                                break;
                            }
                            let init_path = src_dir.join(&rel_path).join("__init__.spl");
                            if init_path.is_file() {
                                let dep_canonical = safe_canonicalize(&init_path);
                                found_deps.insert(dep_canonical);
                                break;
                            }
                        }
                    }
                }
            }

            let mut found_deps: Vec<_> = found_deps.into_iter().collect();
            found_deps.sort();
            for dep in found_deps {
                if queued.insert(dep.clone()) {
                    queue.push_back(dep);
                }
            }

            files.push((canonical.clone(), source));
        }

        files.sort_by(|a, b| a.0.cmp(&b.0));
        files.dedup_by(|a, b| same_file_path(&a.0, &b.0));
        Ok(files)
    }

    /// Deduplicate files by canonical path for compilation.
    /// Returns indices into the original file list of files to actually compile.
    pub(crate) fn deduplicate_for_compilation(files: &[PathBuf]) -> Vec<usize> {
        let mut seen = std::collections::HashSet::new();
        let mut indices = Vec::new();
        for (i, path) in files.iter().enumerate() {
            let canonical = safe_canonicalize(path);
            if seen.insert(canonical) {
                indices.push(i);
            }
        }
        indices
    }
}

pub(crate) fn extract_reachable_module_paths(
    module: &simple_parser::ast::Module,
    from_file: &Path,
    resolver: &mut crate::module_resolver::ModuleResolver,
) -> Vec<PathBuf> {
    use simple_parser::ast::{
        AutoImportStmt, CommonUseStmt, ExportUseStmt, ImportTarget, ModDecl, ModulePath, MultiUse, Node, UseStmt,
    };

    fn resolve_candidate(
        resolver: &mut crate::module_resolver::ModuleResolver,
        from_file: &Path,
        path: &ModulePath,
        target: Option<&ImportTarget>,
    ) -> Option<PathBuf> {
        match target {
            Some(ImportTarget::Single(name)) | Some(ImportTarget::Aliased { name, .. }) => {
                let mut module_segments = path.segments.clone();
                module_segments.push(name.clone());
                let module_path = ModulePath::new(module_segments);
                if let Ok(resolved) = resolver.resolve(&module_path, from_file) {
                    return Some(safe_canonicalize(&resolved.path));
                }
            }
            _ => {}
        }
        resolver
            .resolve(path, from_file)
            .ok()
            .map(|resolved| safe_canonicalize(&resolved.path))
    }

    fn push_dep(
        deps: &mut Vec<PathBuf>,
        resolver: &mut crate::module_resolver::ModuleResolver,
        from_file: &Path,
        path: &ModulePath,
        target: Option<&ImportTarget>,
    ) {
        if let Some(resolved) = resolve_candidate(resolver, from_file, path, target) {
            if !deps.iter().any(|existing| same_file_path(existing, &resolved)) {
                deps.push(resolved);
            }
        }
    }

    let mut deps = Vec::new();
    for item in &module.items {
        match item {
            Node::UseStmt(UseStmt { path, target, .. }) => push_dep(&mut deps, resolver, from_file, path, Some(target)),
            Node::CommonUseStmt(CommonUseStmt { path, target, .. }) => {
                push_dep(&mut deps, resolver, from_file, path, Some(target))
            }
            Node::ExportUseStmt(ExportUseStmt { path, target, .. }) => {
                push_dep(&mut deps, resolver, from_file, path, Some(target))
            }
            Node::MultiUse(MultiUse { imports, .. }) => {
                for (path, target) in imports {
                    push_dep(&mut deps, resolver, from_file, path, Some(target));
                }
            }
            Node::AutoImportStmt(AutoImportStmt { path, .. }) => push_dep(&mut deps, resolver, from_file, path, None),
            Node::ModDecl(ModDecl { name, body, .. }) if body.is_none() => {
                let path = ModulePath::new(vec![name.clone()]);
                push_dep(&mut deps, resolver, from_file, &path, None);
            }
            _ => {}
        }
    }
    deps
}
