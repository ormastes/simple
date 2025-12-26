# Interpreter-Like Workflow Plan

## Overview

This document describes how to achieve an interpreter-like developer experience while using ahead-of-time compilation. The goal: run `simple myfile.simple` and have it "just work" like Python or JavaScript.

---

## Workflow

```
┌─────────────────────────────────────────────────────────────────────┐
│                  Interpreter-Like Workflow                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│    User runs: simple myfile.simple                                   │
│                    │                                                 │
│                    ▼                                                 │
│    ┌──────────────────────────────────┐                             │
│    │  Check if recompilation needed   │                             │
│    │  (compare source hash vs cache)  │                             │
│    └──────────────┬───────────────────┘                             │
│                   │                                                  │
│         ┌─────────┴─────────┐                                       │
│         │                   │                                        │
│    needs compile       up-to-date                                    │
│         │                   │                                        │
│         ▼                   │                                        │
│    ┌────────────┐           │                                        │
│    │  Compile   │           │                                        │
│    │  to .smf   │           │                                        │
│    └─────┬──────┘           │                                        │
│          │                  │                                        │
│          ▼                  ▼                                        │
│    ┌───────────────────────────┐                                    │
│    │     Load .smf module      │                                    │
│    └─────────────┬─────────────┘                                    │
│                  │                                                   │
│                  ▼                                                   │
│    ┌───────────────────────────┐                                    │
│    │     Execute main()        │                                    │
│    └───────────────────────────┘                                    │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
simple-cli/
├── Cargo.toml
└── src/
    ├── main.rs             # CLI entry point
    ├── runner.rs           # Run workflow
    ├── cache.rs            # Compilation cache
    ├── watch.rs            # Watch mode
    └── repl.rs             # Interactive REPL
```

---

## CLI Implementation

### Main Entry Point (main.rs)

```rust
// simple-cli/src/main.rs

mod runner;
mod cache;
mod watch;
mod repl;

use std::path::PathBuf;
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "simple")]
#[command(about = "The Simple programming language")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Source file to run
    file: Option<PathBuf>,

    /// Enable watch mode (rerun on file change)
    #[arg(short, long)]
    watch: bool,

    /// Force recompilation
    #[arg(long)]
    rebuild: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// Run a Simple program
    Run {
        file: PathBuf,
        #[arg(short, long)]
        watch: bool,
    },

    /// Compile without running
    Build {
        file: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Start interactive REPL
    Repl,

    /// Check syntax without compiling
    Check {
        file: PathBuf,
    },

    /// Format source code
    Fmt {
        file: PathBuf,
    },

    /// Clean build cache
    Clean,
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Some(Commands::Run { file, watch }) => {
            if watch {
                watch::run_watch(&file)
            } else {
                runner::run(&file, cli.rebuild, cli.verbose)
            }
        }

        Some(Commands::Build { file, output }) => {
            runner::build(&file, output.as_deref(), cli.verbose)
        }

        Some(Commands::Repl) => {
            repl::start()
        }

        Some(Commands::Check { file }) => {
            runner::check(&file)
        }

        Some(Commands::Fmt { file }) => {
            runner::format(&file)
        }

        Some(Commands::Clean) => {
            cache::clean()
        }

        None => {
            // Default: run file if provided, else REPL
            if let Some(file) = cli.file {
                if cli.watch {
                    watch::run_watch(&file)
                } else {
                    runner::run(&file, cli.rebuild, cli.verbose)
                }
            } else {
                repl::start()
            }
        }
    };

    if let Err(e) = result {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}
```

### Runner (runner.rs)

```rust
// simple-cli/src/runner.rs

use std::path::Path;
use std::time::Instant;

use simple_compiler::CompilerPipeline;
use simple_loader::{ModuleLoader, ModuleRegistry};

use crate::cache::CompilationCache;

/// Run a Simple source file
pub fn run(file: &Path, force_rebuild: bool, verbose: bool) -> Result<(), String> {
    let start = Instant::now();

    // Initialize systems
    let cache = CompilationCache::load()?;
    let mut compiler = CompilerPipeline::new()?;
    let loader = ModuleLoader::new();

    // Determine output path
    let output = cache.output_path(file);

    // Check if recompilation needed
    let needs_compile = force_rebuild || cache.needs_recompile(file, &output)?;

    if needs_compile {
        if verbose {
            println!("Compiling {}...", file.display());
        }

        let compile_start = Instant::now();

        // Compile to .smf
        compiler.compile(file, &output)
            .map_err(|e| format!("Compilation failed: {:?}", e))?;

        if verbose {
            println!("Compiled in {:?}", compile_start.elapsed());
        }

        // Update cache
        cache.record_build(file, &output)?;
    } else if verbose {
        println!("Using cached build for {}", file.display());
    }

    // Load module
    if verbose {
        println!("Loading {}...", output.display());
    }

    let module = loader.load(&output)
        .map_err(|e| format!("Failed to load: {:?}", e))?;

    // Find and call main
    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point()
        .ok_or("No main function found")?;

    if verbose {
        println!("Running (total startup: {:?})", start.elapsed());
        println!("---");
    }

    // Execute
    let exit_code = main();

    if verbose {
        println!("---");
        println!("Exited with code {}", exit_code);
    }

    if exit_code != 0 {
        std::process::exit(exit_code);
    }

    Ok(())
}

/// Compile without running
pub fn build(file: &Path, output: Option<&Path>, verbose: bool) -> Result<(), String> {
    let cache = CompilationCache::load()?;
    let mut compiler = CompilerPipeline::new()?;

    let output = output
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| cache.output_path(file));

    if verbose {
        println!("Compiling {} -> {}", file.display(), output.display());
    }

    let start = Instant::now();

    compiler.compile(file, &output)
        .map_err(|e| format!("Compilation failed: {:?}", e))?;

    if verbose {
        println!("Done in {:?}", start.elapsed());
    }

    Ok(())
}

/// Check syntax without compiling
pub fn check(file: &Path) -> Result<(), String> {
    let source = std::fs::read_to_string(file)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    let mut parser = simple_parser::SimpleParser::new()?;

    match parser.parse(&source) {
        Ok(_) => {
            println!("✓ {} is valid", file.display());
            Ok(())
        }
        Err(e) => {
            println!("✗ {}", e);
            Err("Syntax check failed".into())
        }
    }
}

/// Format source code
pub fn format(file: &Path) -> Result<(), String> {
    // TODO: Implement formatter
    println!("Formatting not yet implemented");
    Ok(())
}
```

### Compilation Cache (cache.rs)

```rust
// simple-cli/src/cache.rs

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

use serde::{Deserialize, Serialize};

/// Tracks compiled files to avoid unnecessary recompilation
#[derive(Serialize, Deserialize)]
pub struct CompilationCache {
    /// Build directory
    build_dir: PathBuf,
    /// Source file -> build info
    entries: HashMap<PathBuf, CacheEntry>,
    /// Cache file path
    #[serde(skip)]
    cache_file: PathBuf,
}

#[derive(Serialize, Deserialize)]
pub struct CacheEntry {
    /// Source file hash
    source_hash: u64,
    /// Last modification time
    source_mtime: u64,
    /// Output file path
    output_path: PathBuf,
    /// Compile timestamp
    compile_time: u64,
    /// Dependencies (imported modules)
    dependencies: Vec<PathBuf>,
}

impl CompilationCache {
    /// Load or create cache
    pub fn load() -> Result<Self, String> {
        let cache_dir = Self::cache_dir();
        let cache_file = cache_dir.join("cache.json");
        let build_dir = cache_dir.join("build");

        // Ensure directories exist
        fs::create_dir_all(&build_dir)
            .map_err(|e| format!("Failed to create cache dir: {}", e))?;

        // Load existing cache or create new
        let cache = if cache_file.exists() {
            let data = fs::read_to_string(&cache_file)
                .map_err(|e| format!("Failed to read cache: {}", e))?;
            let mut cache: CompilationCache = serde_json::from_str(&data)
                .unwrap_or_else(|_| CompilationCache::new(build_dir.clone()));
            cache.cache_file = cache_file;
            cache
        } else {
            let mut cache = CompilationCache::new(build_dir);
            cache.cache_file = cache_file;
            cache
        };

        Ok(cache)
    }

    fn new(build_dir: PathBuf) -> Self {
        Self {
            build_dir,
            entries: HashMap::new(),
            cache_file: PathBuf::new(),
        }
    }

    /// Get cache directory
    fn cache_dir() -> PathBuf {
        // Use XDG_CACHE_HOME on Linux, appropriate dirs on other platforms
        dirs::cache_dir()
            .unwrap_or_else(|| PathBuf::from("."))
            .join("simple")
    }

    /// Get output path for source file
    pub fn output_path(&self, source: &Path) -> PathBuf {
        let name = source.file_stem()
            .unwrap_or_default()
            .to_string_lossy();

        // Include hash of full path to handle same-named files
        let path_hash = hash_path(source);

        self.build_dir.join(format!("{}_{:016x}.smf", name, path_hash))
    }

    /// Check if recompilation is needed
    pub fn needs_recompile(&self, source: &Path, output: &Path) -> Result<bool, String> {
        // Output doesn't exist -> need compile
        if !output.exists() {
            return Ok(true);
        }

        // Get source metadata
        let source_meta = fs::metadata(source)
            .map_err(|e| format!("Failed to stat source: {}", e))?;

        let source_mtime = source_meta.modified()
            .map_err(|e| format!("Failed to get mtime: {}", e))?
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Check cache entry
        let canonical = source.canonicalize()
            .unwrap_or_else(|_| source.to_path_buf());

        if let Some(entry) = self.entries.get(&canonical) {
            // Check if source was modified
            if entry.source_mtime >= source_mtime {
                // Also check dependencies
                for dep in &entry.dependencies {
                    if let Ok(dep_meta) = fs::metadata(dep) {
                        if let Ok(dep_mtime) = dep_meta.modified() {
                            let dep_mtime = dep_mtime
                                .duration_since(SystemTime::UNIX_EPOCH)
                                .unwrap()
                                .as_secs();
                            if dep_mtime > entry.compile_time {
                                return Ok(true);
                            }
                        }
                    }
                }
                return Ok(false);
            }
        }

        // Check by comparing modification times
        let output_meta = fs::metadata(output)
            .map_err(|e| format!("Failed to stat output: {}", e))?;

        let output_mtime = output_meta.modified()
            .map_err(|e| format!("Failed to get mtime: {}", e))?
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Ok(source_mtime > output_mtime)
    }

    /// Record a successful build
    pub fn record_build(&mut self, source: &Path, output: &Path) -> Result<(), String> {
        let canonical = source.canonicalize()
            .unwrap_or_else(|_| source.to_path_buf());

        let source_content = fs::read(source)
            .map_err(|e| format!("Failed to read source: {}", e))?;

        let source_hash = hash_bytes(&source_content);

        let source_mtime = fs::metadata(source)
            .and_then(|m| m.modified())
            .map(|t| t.duration_since(SystemTime::UNIX_EPOCH).unwrap().as_secs())
            .unwrap_or(0);

        let compile_time = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        self.entries.insert(canonical, CacheEntry {
            source_hash,
            source_mtime,
            output_path: output.to_path_buf(),
            compile_time,
            dependencies: Vec::new(),  // TODO: Track dependencies
        });

        self.save()
    }

    /// Save cache to disk
    fn save(&self) -> Result<(), String> {
        let data = serde_json::to_string_pretty(self)
            .map_err(|e| format!("Failed to serialize cache: {}", e))?;

        fs::write(&self.cache_file, data)
            .map_err(|e| format!("Failed to write cache: {}", e))?;

        Ok(())
    }
}

/// Clean the cache
pub fn clean() -> Result<(), String> {
    let cache_dir = CompilationCache::cache_dir();

    if cache_dir.exists() {
        fs::remove_dir_all(&cache_dir)
            .map_err(|e| format!("Failed to clean cache: {}", e))?;
        println!("Cleaned cache at {}", cache_dir.display());
    } else {
        println!("Cache directory doesn't exist");
    }

    Ok(())
}

fn hash_bytes(data: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;

    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    hasher.finish()
}

fn hash_path(path: &Path) -> u64 {
    use std::hash::{Hash, Hasher};
    use std::collections::hash_map::DefaultHasher;

    let mut hasher = DefaultHasher::new();
    path.hash(&mut hasher);
    hasher.finish()
}
```

### Watch Mode (watch.rs)

```rust
// simple-cli/src/watch.rs

use std::path::Path;
use std::time::{Duration, Instant};

use notify::{Watcher, RecursiveMode, Event, EventKind};
use std::sync::mpsc::{channel, RecvTimeoutError};

use crate::runner;

/// Run file and rerun on changes
pub fn run_watch(file: &Path) -> Result<(), String> {
    println!("Watching {} for changes...", file.display());
    println!("Press Ctrl+C to stop\n");

    // Initial run
    let _ = run_and_report(file);

    // Set up file watcher
    let (tx, rx) = channel();

    let mut watcher = notify::recommended_watcher(move |res: Result<Event, _>| {
        if let Ok(event) = res {
            match event.kind {
                EventKind::Modify(_) | EventKind::Create(_) => {
                    let _ = tx.send(());
                }
                _ => {}
            }
        }
    })
    .map_err(|e| format!("Failed to create watcher: {}", e))?;

    // Watch the file and its directory (for new imports)
    watcher.watch(file, RecursiveMode::NonRecursive)
        .map_err(|e| format!("Failed to watch file: {}", e))?;

    if let Some(parent) = file.parent() {
        watcher.watch(parent, RecursiveMode::Recursive)
            .map_err(|e| format!("Failed to watch directory: {}", e))?;
    }

    // Debounce settings
    let debounce = Duration::from_millis(200);
    let mut last_run = Instant::now();

    loop {
        match rx.recv_timeout(Duration::from_millis(100)) {
            Ok(()) => {
                // Debounce rapid changes
                if last_run.elapsed() > debounce {
                    println!("\n[change detected, rerunning...]\n");
                    let _ = run_and_report(file);
                    last_run = Instant::now();
                }
            }
            Err(RecvTimeoutError::Timeout) => {
                // Continue waiting
            }
            Err(RecvTimeoutError::Disconnected) => {
                break;
            }
        }
    }

    Ok(())
}

fn run_and_report(file: &Path) -> Result<(), ()> {
    let start = Instant::now();

    match runner::run(file, false, false) {
        Ok(()) => {
            println!("\n[completed in {:?}]", start.elapsed());
            Ok(())
        }
        Err(e) => {
            eprintln!("\n[error: {}]", e);
            Err(())
        }
    }
}
```

### REPL (repl.rs)

```rust
// simple-cli/src/repl.rs

use std::io::{self, Write};

use simple_parser::SimpleParser;
use simple_compiler::CompilerPipeline;

/// Interactive REPL
pub fn start() -> Result<(), String> {
    println!("Simple REPL v0.1.0");
    println!("Type :help for help, :quit to exit\n");

    let mut parser = SimpleParser::new()?;
    let mut context = ReplContext::new();

    loop {
        // Print prompt
        print!("> ");
        io::stdout().flush().ok();

        // Read input
        let mut input = String::new();
        if io::stdin().read_line(&mut input).is_err() {
            break;
        }

        let input = input.trim();

        // Handle commands
        if input.starts_with(':') {
            match input {
                ":quit" | ":q" => break,
                ":help" | ":h" => print_help(),
                ":clear" | ":c" => context.clear(),
                ":vars" | ":v" => context.print_vars(),
                cmd => println!("Unknown command: {}", cmd),
            }
            continue;
        }

        // Handle empty input
        if input.is_empty() {
            continue;
        }

        // Handle multi-line input (if ends with :)
        let full_input = if input.ends_with(':') {
            read_block(input)?
        } else {
            input.to_string()
        };

        // Evaluate
        match context.eval(&mut parser, &full_input) {
            Ok(result) => {
                if !result.is_empty() && result != "nil" {
                    println!("{}", result);
                }
            }
            Err(e) => {
                println!("Error: {}", e);
            }
        }
    }

    println!("Goodbye!");
    Ok(())
}

fn print_help() {
    println!("Commands:");
    println!("  :quit, :q    Exit REPL");
    println!("  :help, :h    Show this help");
    println!("  :clear, :c   Clear defined variables");
    println!("  :vars, :v    Show defined variables");
    println!();
    println!("Enter Simple expressions or statements.");
    println!("Use : at end of line for multi-line input.");
}

fn read_block(first_line: &str) -> Result<String, String> {
    let mut lines = vec![first_line.to_string()];

    loop {
        print!("... ");
        io::stdout().flush().ok();

        let mut line = String::new();
        if io::stdin().read_line(&mut line).is_err() {
            break;
        }

        let line = line.trim_end();

        // Empty line ends block
        if line.is_empty() {
            break;
        }

        lines.push(line.to_string());
    }

    Ok(lines.join("\n"))
}

struct ReplContext {
    history: Vec<String>,
    variables: std::collections::HashMap<String, String>,
    counter: usize,
}

impl ReplContext {
    fn new() -> Self {
        Self {
            history: Vec::new(),
            variables: std::collections::HashMap::new(),
            counter: 0,
        }
    }

    fn eval(&mut self, parser: &mut SimpleParser, input: &str) -> Result<String, String> {
        // Wrap in function for compilation
        self.counter += 1;
        let wrapper = format!(
            "fn __repl_{}():\n    {}",
            self.counter,
            input.lines()
                .map(|l| format!("    {}", l))
                .collect::<Vec<_>>()
                .join("\n")
        );

        // Parse
        let _ast = parser.parse(&wrapper)
            .map_err(|e| format!("{:?}", e))?;

        // For now, just echo back
        // TODO: Compile and execute
        self.history.push(input.to_string());

        Ok("(evaluation not yet implemented)".to_string())
    }

    fn clear(&mut self) {
        self.variables.clear();
        println!("Variables cleared");
    }

    fn print_vars(&self) {
        if self.variables.is_empty() {
            println!("No variables defined");
        } else {
            for (name, value) in &self.variables {
                println!("  {} = {}", name, value);
            }
        }
    }
}
```

---

## Startup Time Optimization

For interpreter-like feel, startup must be fast:

### 1. Fast Cache Check

```rust
// Optimized cache check using file modification times only
fn fast_needs_recompile(source: &Path, output: &Path) -> bool {
    // Use std::fs::metadata which is very fast
    match (source.metadata(), output.metadata()) {
        (Ok(src_meta), Ok(out_meta)) => {
            match (src_meta.modified(), out_meta.modified()) {
                (Ok(src_time), Ok(out_time)) => src_time > out_time,
                _ => true,
            }
        }
        _ => true,
    }
}
```

### 2. Memory-Mapped Module Loading

```rust
// Load module with mmap for near-instant loading
fn fast_load(path: &Path) -> Result<LoadedModule, Error> {
    let file = File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };

    // Parse header (first 64 bytes)
    let header = SmfHeader::from_bytes(&mmap[..64])?;

    // Validate
    if !header.is_valid_for_platform() {
        return Err(Error::IncompatiblePlatform);
    }

    // Load is essentially free - actual code pages loaded on demand
    Ok(LoadedModule {
        mmap,
        header,
        // ... lazy symbol table loading
    })
}
```

### 3. Parallel Compilation

```rust
// Compile multiple files in parallel
fn compile_parallel(files: &[PathBuf]) -> Result<(), Error> {
    use rayon::prelude::*;

    files.par_iter()
        .try_for_each(|file| {
            let output = cache.output_path(file);
            if cache.needs_recompile(file, &output)? {
                compile_single(file, &output)?;
            }
            Ok(())
        })
}
```

---

## Complete Usage Examples

```bash
# Run a file (compiles if needed)
simple hello.simple

# Run with watch mode (rerun on file change)
simple --watch hello.simple
simple -w hello.simple

# Force recompile
simple --rebuild hello.simple

# Verbose output (shows compile/load times)
simple -v hello.simple

# Just compile, don't run
simple build hello.simple
simple build hello.simple -o hello.smf

# Check syntax
simple check hello.simple

# Interactive REPL
simple repl
simple  # (no arguments starts REPL)

# Clean build cache
simple clean
```

---

## Performance Targets

| Metric | Target | Notes |
|--------|--------|-------|
| Cached startup | < 50ms | Load .smf, run main |
| Cold compile (small file) | < 200ms | Parse, compile, link |
| Cold compile (medium file) | < 500ms | With type checking |
| Incremental compile | < 100ms | Only changed functions |
| REPL response | < 100ms | Compile + execute expression |

---

## Cargo.toml

```toml
[package]
name = "simple-cli"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "simple"
path = "src/main.rs"

[dependencies]
clap = { version = "4.4", features = ["derive"] }
notify = "6.1"
dirs = "5.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

simple-parser = { path = "../crates/parser" }
simple-compiler = { path = "../crates/compiler" }
simple-loader = { path = "../crates/loader" }
simple-runtime = { path = "../crates/runtime" }
```

---

## Summary

The interpreter-like workflow provides:

1. **Simple command**: `simple myfile.simple` just works
2. **Automatic compilation**: Rebuilds only when source changed
3. **Fast startup**: Cached builds load in < 50ms
4. **Watch mode**: Auto-rerun on file changes
5. **REPL**: Interactive exploration

This gives developers the convenience of interpreted languages while maintaining compiled-language performance.
