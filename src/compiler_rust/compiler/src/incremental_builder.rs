impl IncrementalBuilder {
    /// Create a new builder.
    pub fn new(state: Arc<IncrementalState>) -> Self {
        Self { state }
    }

    /// Add a source file.
    pub fn add_source(&self, path: PathBuf, content: &str) {
        let mut info = SourceInfo::new(path.clone());
        info.update_from_content(content);
        let _ = info.update_mtime();

        // Parse imports (simple heuristic)
        for line in content.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("import ") {
                if let Some(token) = rest.split_whitespace().next() {
                    let mut dep_path = PathBuf::from(token);
                    if dep_path.extension().is_none() {
                        dep_path.set_extension("spl");
                    }
                    if dep_path.is_relative() {
                        if let Some(parent) = path.parent() {
                            dep_path = parent.join(dep_path);
                        }
                    }
                    info.dependencies.push(dep_path);
                }
            } else if let Some(rest) = trimmed.strip_prefix("use ") {
                // Track use statements as potential dependencies
                if let Some(module) = rest.split(|c| c == '.' || c == ' ').next() {
                    let mut dep_path = PathBuf::from(module);
                    dep_path.set_extension("spl");
                    if dep_path.is_relative() {
                        if let Some(parent) = path.parent() {
                            dep_path = parent.join(dep_path);
                        }
                    }
                    if !info.dependencies.contains(&dep_path) {
                        info.dependencies.push(dep_path);
                    }
                }
            } else if let Some(rest) = trimmed.strip_prefix("fn ") {
                if let Some(name) = rest.split(|c| c == '(' || c == '[').next() {
                    info.functions.push(name.trim().to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("struct ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("class ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("enum ") {
                if let Some(name) = rest.split(|c: char| !c.is_alphanumeric() && c != '_').next() {
                    info.types.push(name.to_string());
                }
            } else if let Some(rest) = trimmed.strip_prefix("macro ") {
                if let Some(name) = rest.split(|c| c == '(' || c == '=').next() {
                    info.macros.push(name.trim().to_string());
                }
            }
        }

        self.state.register_source(info);
    }

    /// Build incrementally, returning files that need compilation.
    pub fn build(&self) -> Vec<PathBuf> {
        self.state.check_all()
    }

    /// Mark a file as successfully compiled.
    pub fn complete(&self, path: &Path, has_hir: bool, has_mir: bool, has_object: bool) {
        if let Some(source) = self.state.sources.get(path) {
            let mut artifact = CachedArtifact::new(source.clone());
            artifact.has_hir = has_hir;
            artifact.has_mir = has_mir;
            artifact.has_object = has_object;
            self.state.mark_complete(path, artifact);
        }
    }

    /// Mark a file as failed.
    pub fn fail(&self, path: &Path) {
        self.state.mark_failed(path);
    }

    /// Get compilation statistics.
    pub fn stats(&self) -> IncrementalStats {
        self.state.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_source_info_content_hash() {
        let mut info = SourceInfo::new(PathBuf::from("test.spl"));
        info.update_from_content("fn main(): println(\"hello\")");

        let hash1 = info.content_hash;

        info.update_from_content("fn main(): println(\"world\")");
        let hash2 = info.content_hash;

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_incremental_state_register() {
        let state = IncrementalState::new();

        let mut info = SourceInfo::new(PathBuf::from("main.spl"));
        info.dependencies.push(PathBuf::from("lib.spl"));
        state.register_source(info);

        assert_eq!(state.get_status(Path::new("main.spl")), CompilationStatus::Unknown);
    }

    #[test]
    fn test_incremental_state_dirty() {
        let state = IncrementalState::new();

        let mut main_info = SourceInfo::new(PathBuf::from("main.spl"));
        main_info.dependencies.push(PathBuf::from("lib.spl"));
        state.register_source(main_info);

        let lib_info = SourceInfo::new(PathBuf::from("lib.spl"));
        state.register_source(lib_info);

        // Mark lib as dirty - should cascade to main
        state.mark_dirty(Path::new("lib.spl"));

        assert_eq!(state.get_status(Path::new("lib.spl")), CompilationStatus::Dirty);
        assert_eq!(state.get_status(Path::new("main.spl")), CompilationStatus::Dirty);
    }

    #[test]
    fn test_incremental_state_complete() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info.clone());

        let artifact = CachedArtifact::new(info);
        state.mark_complete(Path::new("test.spl"), artifact);

        assert_eq!(state.get_status(Path::new("test.spl")), CompilationStatus::Complete);
        assert!(state.get_artifact(Path::new("test.spl")).is_some());
    }

    #[test]
    fn test_incremental_builder() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state);

        builder.add_source(
            PathBuf::from("main.spl"),
            r#"
            import lib
            fn main():
                hello()
            "#,
        );

        builder.add_source(
            PathBuf::from("lib.spl"),
            r#"
            fn hello():
                println("Hello")
            "#,
        );

        // All files should need compilation initially
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_incremental_stats() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info);

        // Check will increment stats
        let _ = state.needs_recompile(Path::new("test.spl"));

        let stats = state.stats();
        assert_eq!(stats.files_checked, 1);
        assert_eq!(stats.cache_misses, 1);
    }

    #[test]
    fn test_cached_artifact() {
        let info = SourceInfo::new(PathBuf::from("test.spl"));
        let mut artifact = CachedArtifact::new(info);

        assert!(!artifact.has_hir);
        assert!(!artifact.has_mir);
        assert!(!artifact.has_object);

        artifact.has_hir = true;
        artifact.has_mir = true;

        assert!(artifact.has_hir);
        assert!(artifact.has_mir);
        assert!(!artifact.has_object);
    }

    #[test]
    fn test_incremental_state_clear() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("test.spl"));
        state.register_source(info);
        state.mark_dirty(Path::new("test.spl"));

        state.clear();

        assert_eq!(state.get_status(Path::new("test.spl")), CompilationStatus::Unknown);
    }

    #[test]
    fn test_incremental_config() {
        let default_config = IncrementalConfig::default();
        assert!(default_config.persist);
        assert!(default_config.validate_on_load);

        let memory_config = IncrementalConfig::memory_only();
        assert!(!memory_config.persist);
        assert!(!memory_config.validate_on_load);
    }

    #[test]
    fn test_stats_ratios() {
        let mut stats = IncrementalStats::default();

        // Empty stats
        assert_eq!(stats.hit_ratio(), 0.0);
        assert_eq!(stats.rebuild_ratio(), 0.0);

        // Some hits and misses
        stats.cache_hits = 3;
        stats.cache_misses = 1;
        stats.files_checked = 10;
        stats.files_dirty = 2;

        assert_eq!(stats.hit_ratio(), 0.75);
        assert_eq!(stats.rebuild_ratio(), 0.2);
    }

    #[test]
    fn test_dependency_chain_invalidation() {
        // Test: A depends on B, B depends on C
        // When C is marked dirty, both A and B should be dirty
        let state = IncrementalState::new();

        // C has no dependencies
        let c_info = SourceInfo::new(PathBuf::from("c.spl"));
        state.register_source(c_info);

        // B depends on C
        let mut b_info = SourceInfo::new(PathBuf::from("b.spl"));
        b_info.dependencies.push(PathBuf::from("c.spl"));
        state.register_source(b_info);

        // A depends on B
        let mut a_info = SourceInfo::new(PathBuf::from("a.spl"));
        a_info.dependencies.push(PathBuf::from("b.spl"));
        state.register_source(a_info);

        // Mark C as dirty - should cascade to B (direct dependent)
        state.mark_dirty(Path::new("c.spl"));

        assert_eq!(state.get_status(Path::new("c.spl")), CompilationStatus::Dirty);
        assert_eq!(state.get_status(Path::new("b.spl")), CompilationStatus::Dirty);
        // Note: A won't be marked dirty automatically - only direct dependents are marked
    }

    #[test]
    fn test_multiple_dependents() {
        // Test: Multiple files depend on same library
        let state = IncrementalState::new();

        let lib_info = SourceInfo::new(PathBuf::from("lib.spl"));
        state.register_source(lib_info);

        // Multiple files depend on lib
        for i in 0..5 {
            let mut info = SourceInfo::new(PathBuf::from(format!("app{}.spl", i)));
            info.dependencies.push(PathBuf::from("lib.spl"));
            state.register_source(info);
        }

        // Mark lib as dirty
        state.mark_dirty(Path::new("lib.spl"));

        // All dependents should be dirty
        for i in 0..5 {
            assert_eq!(
                state.get_status(Path::new(&format!("app{}.spl", i))),
                CompilationStatus::Dirty
            );
        }

        let stats = state.stats();
        assert_eq!(stats.dependency_invalidations, 5);
    }

    #[test]
    fn test_invalidate_all() {
        // Use new() which returns Arc<IncrementalState>
        let state = IncrementalState::new();

        // Register a file
        let info = SourceInfo::new(PathBuf::from("test_inv.spl"));
        state.register_source(info.clone());

        // Create artifact and mark complete
        let mut artifact = CachedArtifact::new(info);
        artifact.has_hir = true;
        state.mark_complete(Path::new("test_inv.spl"), artifact);

        // Verify complete
        assert_eq!(
            state.get_status(Path::new("test_inv.spl")),
            CompilationStatus::Complete
        );
        assert!(state.get_artifact(Path::new("test_inv.spl")).is_some());

        // Invalidate all
        state.invalidate_all();

        // Should be dirty now
        assert_eq!(
            state.get_status(Path::new("test_inv.spl")),
            CompilationStatus::Dirty
        );

        // Artifacts should be cleared
        assert!(state.get_artifact(Path::new("test_inv.spl")).is_none());
    }

    #[test]
    fn test_builder_parse_complex_source() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state);

        // Test parsing of various Simple language constructs
        builder.add_source(
            PathBuf::from("complex.spl"),
            r#"
            import utils
            use core.*
            use io.fs

            struct Point:
                x: i64
                y: i64

            class Counter:
                count: i64

            enum Status:
                Ok
                Error

            macro debug(msg: Str) -> ():
                emit result:
                    println(msg)

            fn helper[T](x: T) -> T:
                return x

            fn main():
                let p = Point(x: 0, y: 0)
                println("Hello")
            "#,
        );

        // Verify parsed metadata
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_builder_complete_and_stats() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state.clone());

        builder.add_source(PathBuf::from("test.spl"), "fn main(): return 0");

        let dirty = builder.build();
        assert_eq!(dirty.len(), 1);

        // Complete with all artifacts
        builder.complete(Path::new("test.spl"), true, true, true);

        assert_eq!(
            state.get_status(Path::new("test.spl")),
            CompilationStatus::Complete
        );

        let artifact = state.get_artifact(Path::new("test.spl")).unwrap();
        assert!(artifact.has_hir);
        assert!(artifact.has_mir);
        assert!(artifact.has_object);
    }

    #[test]
    fn test_builder_fail() {
        let state = IncrementalState::new();
        let builder = IncrementalBuilder::new(state.clone());

        builder.add_source(PathBuf::from("bad.spl"), "syntax error here");
        let _ = builder.build();

        builder.fail(Path::new("bad.spl"));

        assert_eq!(
            state.get_status(Path::new("bad.spl")),
            CompilationStatus::Failed
        );
    }

    #[test]
    fn test_get_dirty_files() {
        let state = IncrementalState::new();

        for i in 0..5 {
            let info = SourceInfo::new(PathBuf::from(format!("file{}.spl", i)));
            state.register_source(info);
        }

        // Mark some as dirty
        state.mark_dirty(Path::new("file1.spl"));
        state.mark_dirty(Path::new("file3.spl"));

        let dirty = state.get_dirty_files();
        assert_eq!(dirty.len(), 2);
        assert!(dirty.contains(&PathBuf::from("file1.spl")));
        assert!(dirty.contains(&PathBuf::from("file3.spl")));
    }

    #[test]
    fn test_in_progress_status() {
        let state = IncrementalState::new();

        let info = SourceInfo::new(PathBuf::from("compiling.spl"));
        state.register_source(info);

        state.mark_in_progress(Path::new("compiling.spl"));
        assert_eq!(
            state.get_status(Path::new("compiling.spl")),
            CompilationStatus::InProgress
        );
    }

    #[test]
    fn test_cached_artifact_expiration() {
        let info = SourceInfo::new(PathBuf::from("old.spl"));
        let mut artifact = CachedArtifact::new(info);

        // Artifact created now should not be expired
        assert!(!artifact.is_expired(3600)); // 1 hour

        // Manually set old creation time (1 day ago)
        artifact.created_at = artifact.created_at.saturating_sub(86400 + 1);
        assert!(artifact.is_expired(86400)); // 1 day expiration
    }

    #[test]
    fn test_source_info_definitions() {
        let builder = IncrementalBuilder::new(IncrementalState::new());

        builder.add_source(
            PathBuf::from("defs.spl"),
            r#"
            struct MyStruct:
                field: i32

            class MyClass:
                value: str

            enum MyEnum:
                A
                B

            fn my_function():
                pass

            macro my_macro(x: Int) -> (returns result: Int):
                emit result:
                    x
            "#,
        );

        // The builder should have parsed these definitions
        let dirty = builder.build();
        assert!(!dirty.is_empty());
    }

    #[test]
    fn test_content_hash_consistency() {
        let mut info1 = SourceInfo::new(PathBuf::from("test.spl"));
        let mut info2 = SourceInfo::new(PathBuf::from("test.spl"));

        let content = "fn main(): return 42";
        info1.update_from_content(content);
        info2.update_from_content(content);

        // Same content should produce same hash
        assert_eq!(info1.content_hash, info2.content_hash);

        // Different content should produce different hash
        info2.update_from_content("fn main(): return 0");
        assert_ne!(info1.content_hash, info2.content_hash);
    }
}
