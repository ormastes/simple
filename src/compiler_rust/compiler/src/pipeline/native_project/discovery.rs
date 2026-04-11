//! File discovery: full-scan and entry-closure based .spl file discovery,
//! reachable module path extraction, file deduplication.

use std::collections::{HashSet, VecDeque};
use std::path::{Path, PathBuf};

use super::{collect_spl_files_recursive, safe_canonicalize, same_file_path, NativeProjectBuilder};

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
        files
    }

    fn discover_reachable_files(&self, entry_file: &Path) -> Result<Vec<PathBuf>, String> {
        let canonical_entry = safe_canonicalize(entry_file);

        // Build one resolver per source dir so imports can cross source boundaries.
        let mut resolvers: Vec<crate::module_resolver::ModuleResolver> = self
            .source_dirs
            .iter()
            .map(|dir| {
                let canonical_dir = safe_canonicalize(dir);
                crate::module_resolver::ModuleResolver::new(self.project_root.clone(), canonical_dir)
            })
            .collect();

        // Ensure at least the effective root for the entry file is covered.
        if resolvers.is_empty() {
            let resolver_root = self.effective_source_root_for(&canonical_entry);
            resolvers.push(crate::module_resolver::ModuleResolver::new(
                self.project_root.clone(),
                resolver_root,
            ));
        }

        // Canonicalize source dirs once for the filesystem fallback.
        let canonical_source_dirs: Vec<PathBuf> = self.source_dirs.iter().map(|d| safe_canonicalize(d)).collect();

        let mut queue = VecDeque::from([canonical_entry.clone()]);
        let mut seen = HashSet::new();
        let mut files = Vec::new();

        while let Some(path) = queue.pop_front() {
            let canonical = safe_canonicalize(&path);
            if !seen.insert(canonical.clone()) {
                continue;
            }
            files.push(canonical.clone());

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
            let mut found_deps: Vec<PathBuf> = Vec::new();
            for resolver in &mut resolvers {
                for dep in extract_reachable_module_paths(&module, &canonical, resolver) {
                    let dep_canonical = safe_canonicalize(&dep);
                    if !found_deps
                        .iter()
                        .any(|existing| same_file_path(existing, &dep_canonical))
                    {
                        found_deps.push(dep_canonical);
                    }
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
                                if !found_deps.iter().any(|e| same_file_path(e, &dep_canonical)) {
                                    found_deps.push(dep_canonical);
                                }
                                break;
                            }
                            let mod_path = src_dir.join(&rel_path).join("mod.spl");
                            if mod_path.is_file() {
                                let dep_canonical = safe_canonicalize(&mod_path);
                                if !found_deps.iter().any(|e| same_file_path(e, &dep_canonical)) {
                                    found_deps.push(dep_canonical);
                                }
                                break;
                            }
                            let init_path = src_dir.join(&rel_path).join("__init__.spl");
                            if init_path.is_file() {
                                let dep_canonical = safe_canonicalize(&init_path);
                                if !found_deps.iter().any(|e| same_file_path(e, &dep_canonical)) {
                                    found_deps.push(dep_canonical);
                                }
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
        }

        files.sort();
        files.dedup_by(|a, b| same_file_path(a, b));
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
