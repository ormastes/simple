//! File discovery: full-scan and entry-closure based .spl file discovery,
//! reachable module path extraction, file deduplication.

use std::collections::{HashSet, VecDeque};
use std::path::{Path, PathBuf};

use simple_common::target::TargetArch;

use super::{
    collect_spl_files_recursive, native_project_rust_trace_enabled, safe_canonicalize, same_file_path,
    NativeProjectBuilder,
};

/// Resolve a `@cfg(...)` condition name to an architecture, if it names one.
///
/// Mirrors the arch-alias groups in the pure-Simple preprocessor
/// (`src/compiler/10.frontend/core/parser_preprocessor.spl`
/// `_pp_cfg_condition_matches`) so a whole-file arch gate is recognized the
/// same way here as it is by the self-hosted compiler's own `@cfg`
/// evaluation. Returns `None` for condition names that are not arch aliases
/// (e.g. `test`, `baremetal`, a bare `not(...)` on a non-arch name, or a
/// `"key", "value"` pair) -- those are intentionally left ungated by this
/// discovery-time filter rather than risk excluding a file that should build.
fn cfg_name_to_arch(name: &str) -> Option<TargetArch> {
    match name {
        "x86_64" | "amd64" | "x64" => Some(TargetArch::X86_64),
        "x86" | "i386" | "i686" => Some(TargetArch::X86),
        "aarch64" | "arm64" => Some(TargetArch::Aarch64),
        "arm" | "armv7" | "armv6" | "arm32" => Some(TargetArch::Arm),
        "riscv64" => Some(TargetArch::Riscv64),
        "riscv32" => Some(TargetArch::Riscv32),
        _ => None,
    }
}

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
            let module = parser
                .parse()
                .map_err(|e| format!("failed to parse {} during discovery: {}", canonical.display(), e))?;

            // Try each resolver -- the first hit wins for each dependency.
            let mut found_deps: HashSet<PathBuf> = HashSet::new();
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

            for dep in found_deps {
                if !seen.contains(&dep) {
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
