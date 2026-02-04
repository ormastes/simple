//! Parallel File Parsing (#806)
//!
//! Provides parallel file parsing using rayon for improved compilation performance.
//! All files are parsed concurrently, with thread-safe string interning.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use dashmap::DashMap;
use parking_lot::RwLock;
use rayon::prelude::*;
use simple_parser::ast::{ImportTarget, Module, Node, UseStmt};

use crate::CompileError;

/// Result of parsing a single file.
#[derive(Debug)]
pub struct ParsedFile {
    /// Canonical path to the file.
    pub path: PathBuf,
    /// Parsed module AST.
    pub module: Module,
    /// Files this module imports.
    pub imports: Vec<PathBuf>,
}

/// Thread-safe cache of parsed modules.
pub struct ParallelParseCache {
    /// Parsed modules by canonical path.
    modules: DashMap<PathBuf, Arc<ParsedFile>>,
    /// Errors encountered during parsing.
    errors: RwLock<Vec<(PathBuf, CompileError)>>,
}

impl ParallelParseCache {
    /// Create a new parallel parse cache.
    pub fn new() -> Self {
        Self {
            modules: DashMap::new(),
            errors: RwLock::new(Vec::new()),
        }
    }

    /// Get a parsed module by path.
    pub fn get(&self, path: &Path) -> Option<Arc<ParsedFile>> {
        self.modules.get(path).map(|r| Arc::clone(&r))
    }

    /// Insert a parsed module.
    pub fn insert(&self, path: PathBuf, parsed: ParsedFile) {
        self.modules.insert(path, Arc::new(parsed));
    }

    /// Record a parsing error.
    pub fn record_error(&self, path: PathBuf, error: CompileError) {
        self.errors.write().push((path, error));
    }

    /// Get all errors.
    pub fn take_errors(&self) -> Vec<(PathBuf, CompileError)> {
        std::mem::take(&mut *self.errors.write())
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        !self.errors.read().is_empty()
    }

    /// Get the number of cached modules.
    pub fn len(&self) -> usize {
        self.modules.len()
    }

    /// Check if cache is empty.
    pub fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }
}

impl Default for ParallelParseCache {
    fn default() -> Self {
        Self::new()
    }
}

/// Discover all files that need to be parsed by walking the import graph.
///
/// This performs a quick scan of each file to extract import statements
/// without full parsing. Returns a set of all file paths to parse.
pub fn discover_files(root: &Path) -> Result<HashSet<PathBuf>, CompileError> {
    let mut files = HashSet::new();
    let mut to_scan = vec![root.to_path_buf()];

    while let Some(path) = to_scan.pop() {
        let canonical = path.canonicalize().unwrap_or_else(|_| path.clone());

        if !files.insert(canonical.clone()) {
            continue; // Already visited
        }

        // Quick scan for imports
        let source = fs::read_to_string(&canonical)
            .map_err(|e| CompileError::Io(format!("Failed to read {}: {}", canonical.display(), e)))?;

        // Extract imports with a lightweight scan
        let imports = extract_imports_quick(&source, canonical.parent().unwrap_or(Path::new(".")));

        for import_path in imports {
            if import_path.exists() && !files.contains(&import_path) {
                to_scan.push(import_path);
            }
        }
    }

    Ok(files)
}

/// Quick extraction of import paths from source without full parsing.
///
/// This is a lightweight scan that looks for `use` statements and resolves
/// them to file paths. It's faster than full parsing for discovery.
fn extract_imports_quick(source: &str, base_dir: &Path) -> Vec<PathBuf> {
    let mut imports = Vec::new();

    for line in source.lines() {
        let line = line.trim();

        // Skip comments and empty lines
        if line.starts_with('#') || line.starts_with("//") || line.is_empty() {
            continue;
        }

        // Look for use statements
        if line.starts_with("use ") {
            if let Some(path) = extract_use_path(line, base_dir) {
                imports.push(path);
            }
        }
    }

    imports
}

/// Extract the file path from a use statement line.
fn extract_use_path(line: &str, base_dir: &Path) -> Option<PathBuf> {
    // Remove "use " prefix
    let rest = line.strip_prefix("use ")?.trim();

    // Handle different import syntaxes:
    // - use foo.bar
    // - use foo.bar.*
    // - use foo.bar.{a, b}
    // - use crate.foo.bar

    // Remove trailing .* or .{...} for module path
    let module_path = rest.split(".*").next()?.split(".{").next()?.trim();

    // Split into segments
    let segments: Vec<&str> = module_path
        .split('.')
        .filter(|s| *s != "crate" && !s.is_empty())
        .collect();

    if segments.is_empty() {
        return None;
    }

    // Build file path
    let mut path = base_dir.to_path_buf();
    for segment in segments {
        path = path.join(segment);
    }
    path.set_extension("spl");

    if path.exists() {
        Some(path)
    } else {
        None
    }
}

/// Parse a single file and extract its imports.
fn parse_file(path: &Path, base_dir: &Path) -> Result<ParsedFile, CompileError> {
    let source =
        fs::read_to_string(path).map_err(|e| CompileError::Io(format!("Failed to read {}: {}", path.display(), e)))?;

    let mut parser = simple_parser::Parser::new(&source);
    let module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("Error parsing {}: {}", path.display(), e)))?;

    // Extract imports from AST
    let imports = extract_imports_from_module(&module, base_dir);

    Ok(ParsedFile {
        path: path.to_path_buf(),
        module,
        imports,
    })
}

/// Extract import paths from a parsed module AST.
fn extract_imports_from_module(module: &Module, base_dir: &Path) -> Vec<PathBuf> {
    let mut imports = Vec::new();

    for item in &module.items {
        if let Node::UseStmt(use_stmt) = item {
            if let Some(path) = resolve_use_to_path(use_stmt, base_dir) {
                imports.push(path);
            }
        }
    }

    imports
}

/// Resolve a use statement to a file path.
fn resolve_use_to_path(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // Handle different import targets
    match &use_stmt.target {
        ImportTarget::Single(name) => {
            parts.push(name.clone());
        }
        ImportTarget::Aliased { name, .. } => {
            parts.push(name.clone());
        }
        ImportTarget::Glob => {
            // For glob imports, the path segments already contain the module path
        }
        ImportTarget::Group(_) => {
            // Group imports need special handling - skip for now
            return None;
        }
    }

    let mut resolved = base.to_path_buf();
    for part in &parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");

    if resolved.exists() {
        Some(resolved)
    } else {
        None
    }
}

/// Parse multiple files in parallel using rayon.
///
/// Returns a cache containing all parsed modules, which can then be used
/// for import resolution and further compilation.
pub fn parse_files_parallel(files: &[PathBuf]) -> ParallelParseCache {
    let cache = ParallelParseCache::new();

    files.par_iter().for_each(|path| {
        let base_dir = path.parent().unwrap_or(Path::new("."));
        match parse_file(path, base_dir) {
            Ok(parsed) => {
                cache.insert(path.clone(), parsed);
            }
            Err(err) => {
                cache.record_error(path.clone(), err);
            }
        }
    });

    cache
}

/// Parse all files starting from a root file, in parallel.
///
/// This first discovers all files by walking the import graph,
/// then parses all discovered files in parallel.
pub fn parse_all_parallel(root: &Path) -> Result<ParallelParseCache, CompileError> {
    // Phase 1: Discover all files
    let files = discover_files(root)?;

    // Convert to vec for parallel processing
    let file_list: Vec<PathBuf> = files.into_iter().collect();

    // Phase 2: Parse all files in parallel
    let cache = parse_files_parallel(&file_list);

    // Check for errors
    if cache.has_errors() {
        let errors = cache.take_errors();
        let error_msg = errors
            .into_iter()
            .map(|(path, err)| format!("{}: {:?}", path.display(), err))
            .collect::<Vec<_>>()
            .join("\n");
        return Err(CompileError::Parse(error_msg));
    }

    Ok(cache)
}

/// Flatten a module with its imports using the parallel parse cache.
///
/// This resolves imports and combines them into a single module,
/// similar to `load_module_with_imports` but using cached parsed results.
pub fn flatten_module_with_cache(
    path: &Path,
    cache: &ParallelParseCache,
    visited: &mut HashSet<PathBuf>,
) -> Result<Module, CompileError> {
    let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

    if !visited.insert(canonical.clone()) {
        return Ok(Module {
            name: None,
            items: Vec::new(),
        });
    }

    let parsed = cache
        .get(&canonical)
        .ok_or_else(|| CompileError::Io(format!("Module not found in cache: {}", canonical.display())))?;

    let mut items = Vec::new();

    for item in &parsed.module.items {
        if let Node::UseStmt(use_stmt) = item {
            let base_dir = canonical.parent().unwrap_or(Path::new("."));
            if let Some(import_path) = resolve_use_to_path(use_stmt, base_dir) {
                let imported = flatten_module_with_cache(&import_path, cache, visited)?;
                items.extend(imported.items);
                continue;
            }
        }
        items.push(item.clone());
    }

    Ok(Module {
        name: parsed.module.name.clone(),
        items,
    })
}

/// High-level API: Load a module with all its imports, using parallel parsing.
///
/// This is a drop-in replacement for `load_module_with_imports` that uses
/// parallel parsing for improved performance on large codebases.
pub fn load_module_parallel(path: &Path) -> Result<Module, CompileError> {
    // Parse all files in parallel
    let cache = parse_all_parallel(path)?;

    // Flatten the module with imports
    let mut visited = HashSet::new();
    flatten_module_with_cache(path, &cache, &mut visited)
}

/// Configuration for parallel parsing.
#[derive(Debug, Clone)]
pub struct ParallelConfig {
    /// Number of threads to use. None means use all available.
    pub num_threads: Option<usize>,
    /// Whether to use memory-mapped files.
    pub use_mmap: bool,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        Self {
            num_threads: None,
            use_mmap: false,
        }
    }
}

impl ParallelConfig {
    /// Create a new parallel config with all available threads.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the number of threads to use.
    pub fn with_threads(mut self, n: usize) -> Self {
        self.num_threads = Some(n);
        self
    }

    /// Enable memory-mapped file reading.
    pub fn with_mmap(mut self) -> Self {
        self.use_mmap = true;
        self
    }

    /// Build a rayon thread pool with this configuration.
    pub fn build_thread_pool(&self) -> Result<rayon::ThreadPool, CompileError> {
        let mut builder = rayon::ThreadPoolBuilder::new();

        if let Some(n) = self.num_threads {
            builder = builder.num_threads(n);
        }

        builder
            .build()
            .map_err(|e| CompileError::Io(format!("Failed to create thread pool: {}", e)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::TempDir;

    fn create_test_file(dir: &Path, name: &str, content: &str) -> PathBuf {
        let path = dir.join(name);
        let mut file = fs::File::create(&path).unwrap();
        file.write_all(content.as_bytes()).unwrap();
        path
    }

    #[test]
    fn test_extract_use_path_simple() {
        let base = Path::new("/tmp");
        assert!(extract_use_path("use foo.bar", base).is_none()); // File doesn't exist
    }

    #[test]
    fn test_parallel_parse_cache() {
        let cache = ParallelParseCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
        assert!(!cache.has_errors());
    }

    #[test]
    fn test_parallel_config() {
        let config = ParallelConfig::new().with_threads(4).with_mmap();

        assert_eq!(config.num_threads, Some(4));
        assert!(config.use_mmap);
    }

    #[test]
    fn test_discover_single_file() {
        let temp_dir = TempDir::new().unwrap();
        let main_path = create_test_file(temp_dir.path(), "main.spl", "main = 42");

        let files = discover_files(&main_path).unwrap();
        assert_eq!(files.len(), 1);
        assert!(files.contains(&main_path.canonicalize().unwrap()));
    }

    #[test]
    fn test_discover_with_imports() {
        let temp_dir = TempDir::new().unwrap();

        // Create helper module
        create_test_file(
            temp_dir.path(),
            "helper.spl",
            "fn add(a: i64, b: i64) -> i64:\n    return a + b",
        );

        // Create main file that imports helper
        let main_path = create_test_file(temp_dir.path(), "main.spl", "use helper\nmain = add(1, 2)");

        let files = discover_files(&main_path).unwrap();
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_parse_files_parallel_single() {
        let temp_dir = TempDir::new().unwrap();
        let main_path = create_test_file(temp_dir.path(), "main.spl", "main = 42");

        let files = vec![main_path.canonicalize().unwrap()];
        let cache = parse_files_parallel(&files);

        assert_eq!(cache.len(), 1);
        assert!(!cache.has_errors());
    }

    #[test]
    fn test_parse_files_parallel_multiple() {
        let temp_dir = TempDir::new().unwrap();

        let file1 = create_test_file(temp_dir.path(), "mod1.spl", "fn foo() -> i64:\n    return 1");
        let file2 = create_test_file(temp_dir.path(), "mod2.spl", "fn bar() -> i64:\n    return 2");
        let file3 = create_test_file(temp_dir.path(), "mod3.spl", "fn baz() -> i64:\n    return 3");

        let files = vec![
            file1.canonicalize().unwrap(),
            file2.canonicalize().unwrap(),
            file3.canonicalize().unwrap(),
        ];
        let cache = parse_files_parallel(&files);

        assert_eq!(cache.len(), 3);
        assert!(!cache.has_errors());
    }

    #[test]
    fn test_parse_files_parallel_with_error() {
        let temp_dir = TempDir::new().unwrap();

        // Valid file
        let valid = create_test_file(temp_dir.path(), "valid.spl", "main = 42");

        // Invalid file (syntax error)
        let invalid = create_test_file(temp_dir.path(), "invalid.spl", "fn foo(\n    broken syntax");

        let files = vec![valid.canonicalize().unwrap(), invalid.canonicalize().unwrap()];
        let cache = parse_files_parallel(&files);

        // Should have one valid module and one error
        assert_eq!(cache.len(), 1);
        assert!(cache.has_errors());
    }

    #[test]
    fn test_load_module_parallel() {
        let temp_dir = TempDir::new().unwrap();
        let main_path = create_test_file(temp_dir.path(), "main.spl", "main = 42");

        let module = load_module_parallel(&main_path).unwrap();
        assert!(!module.items.is_empty());
    }

    #[test]
    fn test_load_module_parallel_with_imports() {
        let temp_dir = TempDir::new().unwrap();

        // Create helper module
        create_test_file(
            temp_dir.path(),
            "helper.spl",
            "fn add(a: i64, b: i64) -> i64:\n    return a + b",
        );

        // Create main file that imports helper
        let main_path = create_test_file(temp_dir.path(), "main.spl", "use helper\nmain = 0");

        let module = load_module_parallel(&main_path).unwrap();

        // Should contain items from both main and helper
        // Helper's function + main's assignment
        assert!(module.items.len() >= 2);
    }
}
