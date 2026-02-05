//! Native linker abstraction with mold/lld/ld support.
//!
//! This module provides a high-level interface for native linking,
//! with automatic detection of the best available linker.
//!
//! # Linker Selection Priority
//!
//! 1. **Mold** (Linux only): Fastest linker, 4x faster than lld
//! 2. **LLD**: LLVM's linker, cross-platform, fast
//! 3. **GNU ld**: Fallback, always available on Unix systems
//!
//! # Environment Variables
//!
//! - `SIMPLE_LINKER`: Override linker selection (mold, lld, ld)
//! - `SIMPLE_LINKER_THREADS`: Number of threads for parallel linking
//! - `SIMPLE_LINKER_DEBUG`: Enable verbose linker output

use std::path::{Path, PathBuf};
use std::process::Command;

use super::error::{LinkerError, LinkerResult};

/// Native linker variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeLinker {
    /// Mold: Modern, fast linker (Linux only)
    /// See: https://github.com/rui314/mold
    Mold,
    /// LLD: LLVM's linker (cross-platform)
    Lld,
    /// GNU ld: Traditional linker (fallback)
    Ld,
}

impl NativeLinker {
    /// Detect the best available linker on the system.
    ///
    /// Checks for linkers in order of preference:
    /// 1. Mold (Linux only)
    /// 2. LLD
    /// 3. GNU ld
    ///
    /// Returns `None` if no linker is found.
    pub fn detect() -> Option<Self> {
        // Check environment variable first
        if let Ok(linker) = std::env::var("SIMPLE_LINKER") {
            return Self::from_name(&linker);
        }

        // Mold is only available on Linux
        #[cfg(target_os = "linux")]
        if Self::is_available(Self::Mold) {
            return Some(Self::Mold);
        }

        // Try LLD next (cross-platform)
        if Self::is_available(Self::Lld) {
            return Some(Self::Lld);
        }

        // Fall back to GNU ld
        #[cfg(unix)]
        if Self::is_available(Self::Ld) {
            return Some(Self::Ld);
        }

        None
    }

    /// Parse linker name from string.
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "mold" => Some(Self::Mold),
            "lld" | "ld.lld" => Some(Self::Lld),
            "ld" | "gnu" | "bfd" => Some(Self::Ld),
            _ => None,
        }
    }

    /// Get the linker command name.
    pub fn command(&self) -> &'static str {
        match self {
            Self::Mold => "mold",
            Self::Lld => "ld.lld",
            Self::Ld => "ld",
        }
    }

    /// Get a human-readable name for the linker.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Mold => "mold",
            Self::Lld => "lld",
            Self::Ld => "GNU ld",
        }
    }

    /// Check if this linker is available on the system.
    pub fn is_available(linker: Self) -> bool {
        Command::new(linker.command())
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Get the version of this linker, if available.
    pub fn version(&self) -> Option<String> {
        Command::new(self.command())
            .arg("--version")
            .output()
            .ok()
            .and_then(|o| {
                if o.status.success() {
                    String::from_utf8(o.stdout).ok().map(|s| {
                        // Extract first line as version
                        s.lines().next().unwrap_or("").to_string()
                    })
                } else {
                    None
                }
            })
    }

    /// Check if this linker supports the given target triple.
    pub fn supports_target(&self, _target: &str) -> bool {
        // For now, assume all linkers support the host target
        // In the future, we can add target-specific checks
        true
    }

    /// Link object files into an executable or shared library.
    ///
    /// # Arguments
    ///
    /// * `objects` - List of object files to link
    /// * `output` - Output file path
    /// * `options` - Additional linker options
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` on success, or a `LinkerError` on failure.
    pub fn link(&self, objects: &[PathBuf], output: &Path, options: &LinkOptions) -> LinkerResult<()> {
        // Verify all input files exist
        for obj in objects {
            if !obj.exists() {
                return Err(LinkerError::ObjectNotFound(obj.clone()));
            }
        }

        let mut cmd = Command::new(self.command());

        // Add output file
        cmd.arg("-o").arg(output);

        // Add linker-specific flags
        self.add_common_flags(&mut cmd, options);

        // Add object files
        for obj in objects {
            cmd.arg(obj);
        }

        // Add libraries
        for lib in &options.libraries {
            cmd.arg(format!("-l{}", lib));
        }

        // Add library search paths
        for path in &options.library_paths {
            cmd.arg("-L").arg(path);
        }

        // Add rpath for runtime library loading
        // This ensures the binary can find shared libraries like libsimple_compiler.so
        // Use linker-native syntax (--rpath) not gcc syntax (-Wl,-rpath)
        for path in &options.library_paths {
            cmd.arg(format!("--rpath={}", path.display()));
        }

        // Add extra flags
        for flag in &options.extra_flags {
            cmd.arg(flag);
        }

        // Execute linker
        let output_result = cmd.output()?;

        if output_result.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr).to_string();
            let exit_code = output_result.status.code().unwrap_or(-1);

            // Parse stderr for specific error types
            if stderr.contains("undefined reference") || stderr.contains("undefined symbol") {
                // Extract symbol name if possible
                if let Some(sym) = Self::extract_undefined_symbol(&stderr) {
                    return Err(LinkerError::UndefinedSymbol(sym));
                }
            }

            if stderr.contains("multiple definition") {
                if let Some(sym) = Self::extract_multiple_definition(&stderr) {
                    return Err(LinkerError::MultipleDefinition(sym));
                }
            }

            Err(LinkerError::LinkerFailed {
                exit_code,
                message: format!("{} failed", self.name()),
                stderr,
            })
        }
    }

    /// Add common flags based on linker type and options.
    fn add_common_flags(&self, cmd: &mut Command, options: &LinkOptions) {
        // Thread count for parallel linking
        let threads = options
            .threads
            .or_else(|| std::env::var("SIMPLE_LINKER_THREADS").ok()?.parse().ok());

        match self {
            Self::Mold => {
                if let Some(t) = threads {
                    cmd.arg(format!("--threads={}", t));
                }
                if options.generate_map {
                    if let Some(ref path) = options.map_file {
                        cmd.arg("-Map").arg(path);
                    }
                }
                if options.strip {
                    cmd.arg("-s");
                }
                if options.shared {
                    cmd.arg("-shared");
                }
                if options.pie {
                    cmd.arg("-pie");
                }
            }
            Self::Lld => {
                if let Some(t) = threads {
                    cmd.arg(format!("--threads={}", t));
                }
                if options.generate_map {
                    if let Some(ref path) = options.map_file {
                        cmd.arg(format!("-Map={}", path.display()));
                    }
                }
                if options.strip {
                    cmd.arg("--strip-all");
                }
                if options.shared {
                    cmd.arg("-shared");
                }
                if options.pie {
                    cmd.arg("-pie");
                }
            }
            Self::Ld => {
                if options.generate_map {
                    if let Some(ref path) = options.map_file {
                        cmd.arg(format!("-Map={}", path.display()));
                    }
                }
                if options.strip {
                    cmd.arg("-s");
                }
                if options.shared {
                    cmd.arg("-shared");
                }
                if options.pie {
                    cmd.arg("-pie");
                }
            }
        }

        // Debug output
        if std::env::var("SIMPLE_LINKER_DEBUG").is_ok() || options.verbose {
            cmd.arg("-v");
        }
    }

    /// Extract undefined symbol name from linker error message.
    fn extract_undefined_symbol(stderr: &str) -> Option<String> {
        // Common patterns:
        // - "undefined reference to `symbol'"
        // - "undefined symbol: symbol"
        for line in stderr.lines() {
            if let Some(start) = line.find("undefined reference to `") {
                let rest = &line[start + 24..];
                if let Some(end) = rest.find('\'') {
                    return Some(rest[..end].to_string());
                }
            }
            if let Some(start) = line.find("undefined symbol: ") {
                let rest = &line[start + 18..];
                let end = rest.find(|c: char| c.is_whitespace()).unwrap_or(rest.len());
                return Some(rest[..end].to_string());
            }
        }
        None
    }

    /// Extract multiply-defined symbol name from linker error message.
    fn extract_multiple_definition(stderr: &str) -> Option<String> {
        // Common patterns:
        // - "multiple definition of `symbol'"
        // - "duplicate symbol: symbol"
        for line in stderr.lines() {
            if let Some(start) = line.find("multiple definition of `") {
                let rest = &line[start + 24..];
                if let Some(end) = rest.find('\'') {
                    return Some(rest[..end].to_string());
                }
            }
            if let Some(start) = line.find("duplicate symbol: ") {
                let rest = &line[start + 18..];
                let end = rest.find(|c: char| c.is_whitespace()).unwrap_or(rest.len());
                return Some(rest[..end].to_string());
            }
        }
        None
    }
}

impl std::fmt::Display for NativeLinker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Options for native linking.
#[derive(Debug, Clone, Default)]
pub struct LinkOptions {
    /// Libraries to link against (without -l prefix).
    pub libraries: Vec<String>,
    /// Library search paths.
    pub library_paths: Vec<PathBuf>,
    /// Generate a linker map file.
    pub generate_map: bool,
    /// Path for map file (if generate_map is true).
    pub map_file: Option<PathBuf>,
    /// Strip symbols from output.
    pub strip: bool,
    /// Create a shared library instead of executable.
    pub shared: bool,
    /// Create a position-independent executable.
    pub pie: bool,
    /// Number of threads for parallel linking.
    pub threads: Option<usize>,
    /// Verbose output.
    pub verbose: bool,
    /// Additional flags to pass to the linker.
    pub extra_flags: Vec<String>,
}

impl LinkOptions {
    /// Create new link options with defaults.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a library to link against.
    pub fn library(mut self, name: impl Into<String>) -> Self {
        self.libraries.push(name.into());
        self
    }

    /// Add a library search path.
    pub fn library_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.library_paths.push(path.into());
        self
    }

    /// Enable map file generation.
    pub fn with_map(mut self, path: impl Into<PathBuf>) -> Self {
        self.generate_map = true;
        self.map_file = Some(path.into());
        self
    }

    /// Enable symbol stripping.
    pub fn strip_symbols(mut self) -> Self {
        self.strip = true;
        self
    }

    /// Build as shared library.
    pub fn as_shared(mut self) -> Self {
        self.shared = true;
        self
    }

    /// Build as position-independent executable.
    pub fn as_pie(mut self) -> Self {
        self.pie = true;
        self
    }

    /// Set thread count for parallel linking.
    pub fn with_threads(mut self, threads: usize) -> Self {
        self.threads = Some(threads);
        self
    }

    /// Enable verbose output.
    pub fn verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    /// Add an extra linker flag.
    pub fn flag(mut self, flag: impl Into<String>) -> Self {
        self.extra_flags.push(flag.into());
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linker_from_name() {
        assert_eq!(NativeLinker::from_name("mold"), Some(NativeLinker::Mold));
        assert_eq!(NativeLinker::from_name("MOLD"), Some(NativeLinker::Mold));
        assert_eq!(NativeLinker::from_name("lld"), Some(NativeLinker::Lld));
        assert_eq!(NativeLinker::from_name("ld.lld"), Some(NativeLinker::Lld));
        assert_eq!(NativeLinker::from_name("ld"), Some(NativeLinker::Ld));
        assert_eq!(NativeLinker::from_name("gnu"), Some(NativeLinker::Ld));
        assert_eq!(NativeLinker::from_name("unknown"), None);
    }

    #[test]
    fn test_linker_command() {
        assert_eq!(NativeLinker::Mold.command(), "mold");
        assert_eq!(NativeLinker::Lld.command(), "ld.lld");
        assert_eq!(NativeLinker::Ld.command(), "ld");
    }

    #[test]
    fn test_linker_name() {
        assert_eq!(NativeLinker::Mold.name(), "mold");
        assert_eq!(NativeLinker::Lld.name(), "lld");
        assert_eq!(NativeLinker::Ld.name(), "GNU ld");
    }

    #[test]
    fn test_link_options_builder() {
        let opts = LinkOptions::new()
            .library("c")
            .library("m")
            .library_path("/usr/lib")
            .with_map("/tmp/map.txt")
            .strip_symbols()
            .as_pie()
            .with_threads(4)
            .verbose()
            .flag("--gc-sections");

        assert_eq!(opts.libraries, vec!["c", "m"]);
        assert_eq!(opts.library_paths, vec![PathBuf::from("/usr/lib")]);
        assert!(opts.generate_map);
        assert_eq!(opts.map_file, Some(PathBuf::from("/tmp/map.txt")));
        assert!(opts.strip);
        assert!(opts.pie);
        assert_eq!(opts.threads, Some(4));
        assert!(opts.verbose);
        assert_eq!(opts.extra_flags, vec!["--gc-sections"]);
    }

    #[test]
    fn test_detect_linker() {
        // This test just verifies detection doesn't panic
        // Actual availability depends on system
        let _linker = NativeLinker::detect();
    }

    #[test]
    fn test_extract_undefined_symbol() {
        let stderr = "ld: error: undefined reference to `missing_func'\n";
        assert_eq!(
            NativeLinker::extract_undefined_symbol(stderr),
            Some("missing_func".to_string())
        );

        let stderr2 = "error: undefined symbol: other_func\n";
        assert_eq!(
            NativeLinker::extract_undefined_symbol(stderr2),
            Some("other_func".to_string())
        );
    }

    #[test]
    fn test_extract_multiple_definition() {
        let stderr = "ld: error: multiple definition of `duplicate_sym'\n";
        assert_eq!(
            NativeLinker::extract_multiple_definition(stderr),
            Some("duplicate_sym".to_string())
        );

        let stderr2 = "error: duplicate symbol: other_sym\n";
        assert_eq!(
            NativeLinker::extract_multiple_definition(stderr2),
            Some("other_sym".to_string())
        );
    }
}
