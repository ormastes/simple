# Mold Linker Analysis - Part 3: Detailed Appendices

**Part of:** [Mold Linker Analysis](./mold_linker_analysis_part1.md)

---

        if invocation.emit_relocs {
            args.push("--emit-relocs".to_string());
        }

        if let Some(threads) = invocation.threads {
            args.push(format!("--threads={}", threads));
        }

        for path in &invocation.library_paths {
            args.push("-L".to_string());
            args.push(path.display().to_string());
        }

        for lib in &invocation.libraries {
            args.push("-l".to_string());
            args.push(lib.clone());
        }

        for obj in &invocation.objects {
            args.push(obj.display().to_string());
        }

        args
    }
}

pub struct LldLinker;
pub struct GnuLdLinker;

// Similar implementations for LldLinker and GnuLdLinker...

/// Factory for creating linkers
pub struct LinkerFactory;

impl LinkerFactory {
    pub fn create(kind: NativeLinker) -> Box<dyn Linker> {
        match kind {
            NativeLinker::Mold => Box::new(MoldLinker),
            NativeLinker::Lld => Box::new(LldLinker),
            NativeLinker::Ld => Box::new(GnuLdLinker),
        }
    }

    pub fn detect_best() -> Box<dyn Linker> {
        Self::create(NativeLinker::detect())
    }
}
```

### Pattern 4: Result Type with Rich Error Context

**Purpose:** Provide detailed error information for debugging linker failures.

```rust
/// Linker error with context
#[derive(Debug)]
pub enum LinkerError {
    SpawnFailed {
        linker: String,
        source: std::io::Error,
    },
    WaitFailed {
        linker: String,
        source: std::io::Error,
    },
    LinkFailed {
        linker: String,
        exit_code: Option<i32>,
        stderr: String,
        objects: Vec<PathBuf>,
    },
    MissingOutput,
    NoInputFiles,
    LinkerNotFound {
        linker: String,
    },
    UnsupportedFeature {
        linker: String,
        feature: LinkerFeature,
    },
    UnsupportedTarget {
        linker: String,
        target: String,
    },
}

impl std::fmt::Display for LinkerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpawnFailed { linker, source } =>
                write!(f, "Failed to spawn {}: {}", linker, source),
            Self::WaitFailed { linker, source } =>
                write!(f, "Failed to wait for {}: {}", linker, source),
            Self::LinkFailed { linker, exit_code, stderr, objects } => {
                writeln!(f, "Linking failed with {}", linker)?;
                if let Some(code) = exit_code {
                    writeln!(f, "  Exit code: {}", code)?;
                }
                writeln!(f, "  Input files: {}", objects.len())?;
                if !stderr.is_empty() {
                    writeln!(f, "  Error output:\n{}", stderr)?;
                }
                Ok(())
            }
            Self::MissingOutput =>
                write!(f, "Output path not specified"),
            Self::NoInputFiles =>
                write!(f, "No input files provided"),
            Self::LinkerNotFound { linker } =>
                write!(f, "Linker '{}' not found in PATH", linker),
            Self::UnsupportedFeature { linker, feature } =>
                write!(f, "Linker '{}' does not support {:?}", linker, feature),
            Self::UnsupportedTarget { linker, target } =>
                write!(f, "Linker '{}' does not support target '{}'", linker, target),
        }
    }
}

impl std::error::Error for LinkerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SpawnFailed { source, .. } => Some(source),
            Self::WaitFailed { source, .. } => Some(source),
            _ => None,
        }
    }
}
```

### Pattern 5: Temporary File Guard

**Purpose:** Automatically clean up intermediate object files and artifacts.

```rust
/// Guard for temporary files that cleans up on drop
pub struct TempFileGuard {
    paths: Vec<PathBuf>,
    keep_on_error: bool,
}

impl TempFileGuard {
    pub fn new() -> Self {
        Self {
            paths: Vec::new(),
            keep_on_error: false,
        }
    }

    pub fn keep_on_error(mut self, keep: bool) -> Self {
        self.keep_on_error = keep;
        self
    }

    pub fn add(&mut self, path: impl Into<PathBuf>) -> &PathBuf {
        self.paths.push(path.into());
        self.paths.last().unwrap()
    }

    pub fn create_temp_object(&mut self, prefix: &str) -> std::io::Result<PathBuf> {
        let dir = std::env::temp_dir();
        let name = format!("{}-{}.o", prefix, std::process::id());
        let path = dir.join(name);
        self.paths.push(path.clone());
        Ok(path)
    }

    /// Take ownership of paths, preventing cleanup
    pub fn take(mut self) -> Vec<PathBuf> {
        std::mem::take(&mut self.paths)
    }

    /// Explicitly clean up all files
    pub fn cleanup(&mut self) {
        for path in self.paths.drain(..) {
            let _ = std::fs::remove_file(&path);
        }
    }
}

impl Drop for TempFileGuard {
    fn drop(&mut self) {
        if !self.keep_on_error || !std::thread::panicking() {
            self.cleanup();
        }
    }
}

// Usage:
// let mut temp = TempFileGuard::new().keep_on_error(true);
// let obj1 = temp.create_temp_object("module1")?;
// compile_to_object(source1, &obj1)?;
// let obj2 = temp.create_temp_object("module2")?;
// compile_to_object(source2, &obj2)?;
// link(&[obj1, obj2], output)?;
// temp.cleanup(); // Or let it drop
```

---

## Appendix D: Coding and Design Style Guidelines

### Overview

This section establishes coding conventions for integrating mold linker support into the Simple compiler codebase. These guidelines ensure consistency with existing code and maintainability.

### 1. Module Organization

**File Structure:**
```
src/compiler/src/linker/
├── mod.rs              # Public exports and LinkerKind enum
├── native.rs           # NativeLinker implementation
├── builder.rs          # LinkerBuilder fluent API
├── error.rs            # LinkerError types
├── process.rs          # LinkerProcess RAII wrapper
└── analysis.rs         # Symbol analysis utilities
```

**Module Visibility:**
```rust
// src/compiler/src/linker/mod.rs
mod builder;
mod error;
mod native;
mod process;
mod analysis;

// Public API
pub use builder::LinkerBuilder;
pub use error::LinkerError;
pub use native::{NativeLinker, LinkerOutput};

// Internal use only
pub(crate) use process::LinkerProcess;
pub(crate) use analysis::SymbolAnalyzer;
```

### 2. Naming Conventions

**Types:**
- Use descriptive names: `NativeLinker`, not `NL` or `Linker`
- Suffix error types with `Error`: `LinkerError`
- Suffix builder types with `Builder`: `LinkerBuilder`
- Use `Kind` suffix for enums: `LinkerKind`, `LinkerFeature`

**Functions:**
- Verbs for actions: `link()`, `spawn()`, `detect()`
- Nouns for getters: `name()`, `executable()`, `output()`
- `is_` prefix for boolean checks: `is_available()`, `is_supported()`
- `try_` prefix for fallible operations that return Option: `try_detect()`
- `with_` prefix for builder setters: `with_output()`, `with_threads()`

**Constants:**
- SCREAMING_SNAKE_CASE: `DEFAULT_THREAD_COUNT`, `MAX_RETRIES`

```rust
// Good
pub fn detect_linker() -> NativeLinker { ... }
pub fn is_mold_available() -> bool { ... }
pub fn link_objects(objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> { ... }

// Avoid
pub fn det() -> NativeLinker { ... }  // Too abbreviated
pub fn check_mold() -> bool { ... }   // Not clear what "check" means
pub fn do_link(...) { ... }           // "do_" prefix is redundant
```

### 3. Error Handling Style

**Prefer `Result` over panics:**
```rust
// Good
pub fn link(&self, objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> {
    if objects.is_empty() {
        return Err(LinkerError::NoInputFiles);
    }
    // ...
}

// Avoid panics in library code
pub fn link(&self, objects: &[PathBuf], output: &Path) {
    assert!(!objects.is_empty()); // Only for invariants, not validation
    // ...
}
```

**Use `?` operator with context:**
```rust
use anyhow::{Context, Result};

pub fn link_with_context(invocation: &LinkerInvocation) -> Result<()> {
    let output = Command::new(invocation.linker.executable())
        .args(&invocation.build_args())
        .output()
        .with_context(|| format!(
            "Failed to execute {} linker",
            invocation.linker.name()
        ))?;

    if !output.status.success() {
        anyhow::bail!(
            "Linking failed (exit code {}): {}",
            output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    Ok(())
}
```

### 4. Documentation Style

**Module documentation:**
```rust
//! Native linker integration for Simple compiler.
//!
//! This module provides support for using mold, lld, or GNU ld
//! to produce native executables from compiled object files.
//!
//! # Examples
//!
//! ```rust
//! use simple_compiler::linker::{LinkerBuilder, NativeLinker};
//!
//! let result = LinkerBuilder::new()
//!     .linker(NativeLinker::Mold)
//!     .objects(vec!["main.o".into(), "lib.o".into()])
//!     .output("app")
//!     .build()?
//!     .run()?;
//! ```
//!
//! # Feature Flags
//!
//! - `mold`: Enable mold linker support (default on Linux)
//! - `lld`: Enable LLVM lld linker support
```

**Function documentation:**
```rust
/// Detect the best available linker on the system.
///
/// Linker preference order:
/// 1. mold (if on Linux and available)
/// 2. lld (LLVM linker)
/// 3. ld (GNU linker, fallback)
///
/// # Returns
///
/// The detected linker variant. Never returns an error; always
/// falls back to GNU ld if no other linker is found.
///
/// # Example
///
/// ```rust
/// let linker = NativeLinker::detect();
/// println!("Using linker: {}", linker.name());
/// ```
pub fn detect() -> Self {
    // ...
}
```

### 5. Testing Conventions

**Test organization:**
```rust
#[cfg(test)]
mod tests {
    use super::*;

    // Unit tests for individual functions
    mod detect {
        use super::*;

        #[test]
        fn returns_valid_linker() {
            let linker = NativeLinker::detect();
            assert!(matches!(
                linker,
                NativeLinker::Mold | NativeLinker::Lld | NativeLinker::Ld
            ));
        }

        #[test]
        fn respects_platform() {
            let linker = NativeLinker::detect();
            if cfg!(not(target_os = "linux")) {
                assert_ne!(linker, NativeLinker::Mold);
            }
        }
    }

    // Integration tests with real linker
    mod integration {
        use super::*;
        use tempfile::TempDir;

        #[test]
        #[ignore] // Requires linker installed
        fn links_simple_object() {
            let temp = TempDir::new().unwrap();
            // ... create test object file ...
        }
    }
}
```

**Test helpers:**
```rust
#[cfg(test)]
mod test_helpers {
    use super::*;

    /// Create a minimal ELF object file for testing
    pub fn create_test_object(path: &Path, symbol: &str) -> std::io::Result<()> {
        // Use LLVM or assembler to create test object
        todo!()
    }

    /// Assert linker is available, skip test if not
    pub fn require_linker(linker: NativeLinker) {
        if !linker.is_available() {
            eprintln!("Skipping: {} not available", linker.name());
            return;
        }
    }
}
```

### 6. Configuration Style

**Environment variables:**
```rust
/// Configuration keys for linker selection
pub mod config {
    /// Environment variable to override linker selection
    /// Example: SIMPLE_LINKER=mold
    pub const LINKER_ENV: &str = "SIMPLE_LINKER";

    /// Environment variable to set linker thread count
    /// Example: SIMPLE_LINKER_THREADS=4
    pub const THREADS_ENV: &str = "SIMPLE_LINKER_THREADS";

    /// Environment variable to enable linker debug output
    /// Example: SIMPLE_LINKER_DEBUG=1
    pub const DEBUG_ENV: &str = "SIMPLE_LINKER_DEBUG";
}

impl NativeLinker {
    /// Create linker from environment configuration
    pub fn from_env() -> Self {
        if let Ok(linker) = std::env::var(config::LINKER_ENV) {
            match linker.to_lowercase().as_str() {
                "mold" => return Self::Mold,
                "lld" => return Self::Lld,
                "ld" | "gnu" => return Self::Ld,
                _ => eprintln!("Unknown linker '{}', using auto-detect", linker),
            }
        }
        Self::detect()
    }
}
```

### 7. Logging Style

**Use tracing for structured logging:**
```rust
use tracing::{debug, info, warn, error, instrument, span, Level};

impl NativeLinker {
    #[instrument(skip(objects), fields(linker = %self.name(), object_count = objects.len()))]
    pub fn link(&self, objects: &[PathBuf], output: &Path) -> Result<(), LinkerError> {
        info!(output = %output.display(), "Starting link");

        let start = std::time::Instant::now();

        let result = self.execute_link(objects, output);

        let elapsed = start.elapsed();
        match &result {
            Ok(_) => info!(elapsed_ms = elapsed.as_millis(), "Link completed"),
            Err(e) => error!(error = %e, elapsed_ms = elapsed.as_millis(), "Link failed"),
        }

        result
    }
}
```

### 8. Performance Considerations

**Avoid unnecessary allocations:**
```rust
// Good: Reuse buffer
pub fn build_args(&self, invocation: &LinkerInvocation, buf: &mut Vec<String>) {
    buf.clear();
    buf.push("-o".to_string());
    buf.push(invocation.output.display().to_string());
    // ...
}

// Avoid: Allocate new vec each time
pub fn build_args(&self, invocation: &LinkerInvocation) -> Vec<String> {
    let mut args = Vec::new();
    // ...
    args
}
```

**Lazy detection:**
```rust
use std::sync::OnceLock;

static DETECTED_LINKER: OnceLock<NativeLinker> = OnceLock::new();

impl NativeLinker {
    /// Get cached detected linker (lazy initialization)
    pub fn cached() -> Self {
        *DETECTED_LINKER.get_or_init(Self::detect)
    }
}
```

### 9. Cross-Platform Compatibility

**Platform-specific code:**
```rust
impl NativeLinker {
    pub fn executable(&self) -> &str {
        match self {
            Self::Mold => "mold",
            Self::Lld => {
                #[cfg(target_os = "windows")]
                { "lld-link.exe" }
                #[cfg(not(target_os = "windows"))]
                { "ld.lld" }
            }
            Self::Ld => {
                #[cfg(target_os = "windows")]
                { "ld.exe" }
                #[cfg(not(target_os = "windows"))]
                { "ld" }
            }
        }
    }

    pub fn is_available(&self) -> bool {
        // mold is Linux-only for production use
        if *self == Self::Mold && !cfg!(target_os = "linux") {
            return false;
        }

        which::which(self.executable()).is_ok()
    }
}
```

### 10. API Stability

**Version feature gates:**
```rust
/// Features requiring specific mold version
#[derive(Debug, Clone, Copy)]
pub enum MoldFeature {
    /// Basic linking (all versions)
    Basic,
    /// RISC-V 32-bit support (v1.5.0+)
    Riscv32,
    /// Intel APX support (v2.37.0+)
    IntelApx,
}

impl MoldFeature {
    pub fn min_version(&self) -> (u32, u32, u32) {
        match self {
            Self::Basic => (1, 0, 0),
            Self::Riscv32 => (1, 5, 0),
            Self::IntelApx => (2, 37, 0),
        }
    }
}
```

---

**END OF ANALYSIS**
