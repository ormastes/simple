//! Native linker abstraction with mold/lld/ld support.
//!
//! This module provides a high-level interface for native linking,
//! with automatic detection of the best available linker.
//!
//! # Linker Selection Priority
//!
//! 1. **Mold** (Linux/FreeBSD): Fastest linker, 4x faster than lld
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

use simple_common::target::{LinkerFlavor, Target, TargetOS};

use super::error::{LinkerError, LinkerResult};

/// Native linker variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeLinker {
    /// Mold: Modern, fast linker (Linux/FreeBSD)
    /// See: https://github.com/rui314/mold
    Mold,
    /// LLD: LLVM's linker (cross-platform)
    Lld,
    /// GNU ld: Traditional linker (fallback)
    Ld,
    /// MSVC link.exe: Microsoft Visual C++ linker (Windows)
    Msvc,
}

impl NativeLinker {
    /// Detect the best available linker on the system.
    ///
    /// Checks for linkers in order of preference:
    /// 1. Mold (Linux/FreeBSD)
    /// 2. LLD
    /// 3. GNU ld
    ///
    /// Returns `None` if no linker is found.
    pub fn detect() -> Option<Self> {
        // Check environment variable first
        if let Ok(linker) = std::env::var("SIMPLE_LINKER") {
            return Self::from_name(&linker);
        }

        // Mold is available on Linux and FreeBSD
        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
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

        // On Windows, check for lld-link (MSVC-compatible LLD variant), then MSVC link.exe
        #[cfg(target_os = "windows")]
        {
            if Command::new("lld-link")
                .arg("--version")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
            {
                return Some(Self::Lld);
            }
            if Self::is_available(Self::Msvc) {
                return Some(Self::Msvc);
            }
        }

        None
    }

    /// Detect the best linker for a specific target.
    ///
    /// Uses the target's linker flavor to choose the appropriate linker:
    /// - GNU targets: mold > lld > ld
    /// - MSVC targets: lld-link > link.exe
    /// - WASM targets: wasm-ld
    pub fn detect_for_target(target: &Target) -> Option<Self> {
        // Check environment variable first
        if let Ok(linker) = std::env::var("SIMPLE_LINKER") {
            return Self::from_name(&linker);
        }

        match target.linker_flavor() {
            LinkerFlavor::Msvc => {
                // Prefer lld-link over link.exe
                if Command::new("lld-link")
                    .arg("--version")
                    .output()
                    .map(|o| o.status.success())
                    .unwrap_or(false)
                {
                    return Some(Self::Lld);
                }
                if Self::is_available(Self::Msvc) {
                    return Some(Self::Msvc);
                }
                None
            }
            LinkerFlavor::Gnu => {
                // Standard detection order: mold > lld > ld
                if matches!(target.os, TargetOS::Linux | TargetOS::FreeBSD) && Self::is_available(Self::Mold) {
                    return Some(Self::Mold);
                }
                if Self::is_available(Self::Lld) {
                    return Some(Self::Lld);
                }
                if Self::is_available(Self::Ld) {
                    return Some(Self::Ld);
                }
                None
            }
            LinkerFlavor::WasmLd => {
                // WASM targets use lld's wasm-ld
                if Self::is_available(Self::Lld) {
                    Some(Self::Lld)
                } else {
                    None
                }
            }
        }
    }

    /// Parse linker name from string.
    pub fn from_name(name: &str) -> Option<Self> {
        match name.to_lowercase().as_str() {
            "mold" => Some(Self::Mold),
            "lld" | "ld.lld" | "lld-link" => Some(Self::Lld),
            "ld" | "gnu" | "bfd" => Some(Self::Ld),
            "msvc" | "link" | "link.exe" => Some(Self::Msvc),
            _ => None,
        }
    }

    /// Get the linker command name.
    pub fn command(&self) -> &'static str {
        match self {
            Self::Mold => "mold",
            Self::Lld => {
                // On Windows targets, LLD uses the lld-link frontend
                #[cfg(target_os = "windows")]
                {
                    "lld-link"
                }
                #[cfg(not(target_os = "windows"))]
                {
                    "ld.lld"
                }
            }
            Self::Ld => "ld",
            Self::Msvc => "link.exe",
        }
    }

    /// Get the linker command name for a specific target.
    pub fn command_for_target(&self, target: &Target) -> &'static str {
        match self {
            Self::Lld => match target.linker_flavor() {
                LinkerFlavor::Msvc => "lld-link",
                LinkerFlavor::WasmLd => "wasm-ld",
                LinkerFlavor::Gnu => "ld.lld",
            },
            _ => self.command(),
        }
    }

    /// Get a human-readable name for the linker.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Mold => "mold",
            Self::Lld => "lld",
            Self::Ld => "GNU ld",
            Self::Msvc => "MSVC link.exe",
        }
    }

    /// Check if this linker is available on the system.
    pub fn is_available(linker: Self) -> bool {
        match linker {
            // MSVC link.exe uses /NOLOGO, not --version
            Self::Msvc => Command::new(linker.command())
                .arg("/NOLOGO")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false),
            _ => Command::new(linker.command())
                .arg("--version")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false),
        }
    }

    /// Get the version of this linker, if available.
    pub fn version(&self) -> Option<String> {
        let (cmd, arg) = match self {
            Self::Msvc => (self.command(), "/NOLOGO"),
            _ => (self.command(), "--version"),
        };
        Command::new(cmd)
            .arg(arg)
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

        if matches!(self, Self::Msvc) {
            return self.link_msvc(objects, output, options);
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

        // Add rpath for runtime library loading (not on macOS — use @rpath via install_name_tool)
        for path in &options.library_paths {
            cmd.arg(format!("--rpath={}", path.display()));
        }

        // Add extra flags
        for flag in &options.extra_flags {
            cmd.arg(flag);
        }

        // Entry point
        if let Some(entry) = &options.entry_point {
            cmd.arg("-e").arg(entry);
        }

        // Debug: emit full command when SIMPLE_LINKER_DEBUG is set
        if std::env::var("SIMPLE_LINKER_DEBUG").is_ok() || options.verbose {
            eprintln!("Link command: {:?}", cmd);
        }

        // Execute linker
        let output_result = cmd.output()?;

        if output_result.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr).to_string();
            let exit_code = output_result.status.code().unwrap_or(-1);
            self.classify_link_error(exit_code, &stderr)
        }
    }

    /// MSVC-specific link invocation using /OUT:, /LIBPATH:, etc.
    fn link_msvc(&self, objects: &[PathBuf], output: &Path, options: &LinkOptions) -> LinkerResult<()> {
        let mut cmd = Command::new(self.command());

        // MSVC uses /OUT: for output
        cmd.arg(format!("/OUT:{}", output.display()));

        // Add MSVC-specific flags
        self.add_common_flags(&mut cmd, options);

        // Add object files
        for obj in objects {
            cmd.arg(obj);
        }

        // Add libraries (MSVC uses name.lib, no -l prefix)
        for lib in &options.libraries {
            cmd.arg(format!("{}.lib", lib));
        }

        // Add library search paths (MSVC uses /LIBPATH:)
        for path in &options.library_paths {
            cmd.arg(format!("/LIBPATH:{}", path.display()));
        }

        // No rpath on Windows (PE uses PATH for DLL resolution)

        // Add extra flags
        for flag in &options.extra_flags {
            cmd.arg(flag);
        }

        // Entry point (MSVC uses /ENTRY:)
        if let Some(entry) = &options.entry_point {
            cmd.arg(format!("/ENTRY:{}", entry));
        }

        // Debug: emit full command when SIMPLE_LINKER_DEBUG is set
        if std::env::var("SIMPLE_LINKER_DEBUG").is_ok() || options.verbose {
            eprintln!("Link command: {:?}", cmd);
        }

        // Execute linker
        let output_result = cmd.output()?;

        if output_result.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr).to_string();
            let exit_code = output_result.status.code().unwrap_or(-1);
            self.classify_link_error(exit_code, &stderr)
        }
    }

    /// Classify linker error output into specific error variants.
    fn classify_link_error(&self, exit_code: i32, stderr: &str) -> LinkerResult<()> {
        // Check for undefined symbol patterns (GNU/LLD and MSVC)
        if stderr.contains("undefined reference")
            || stderr.contains("undefined symbol")
            || stderr.contains("unresolved external symbol")
        {
            if let Some(sym) = Self::extract_undefined_symbol(stderr) {
                return Err(LinkerError::UndefinedSymbol(sym));
            }
        }

        // Check for multiple definition patterns (GNU/LLD and MSVC)
        if stderr.contains("multiple definition")
            || stderr.contains("already defined in")
        {
            if let Some(sym) = Self::extract_multiple_definition(stderr) {
                return Err(LinkerError::MultipleDefinition(sym));
            }
        }

        Err(LinkerError::LinkerFailed {
            exit_code,
            message: format!("{} failed", self.name()),
            stderr: stderr.to_string(),
        })
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
            Self::Msvc => {
                if options.generate_map {
                    if let Some(ref path) = options.map_file {
                        cmd.arg(format!("/MAP:{}", path.display()));
                    }
                }
                if options.strip {
                    cmd.arg("/DEBUG:NONE");
                }
                if options.shared {
                    cmd.arg("/DLL");
                }
                // MSVC doesn't have a PIE flag (ASLR is enabled by default)
            }
            _ => {}
        }

        // Debug output
        if std::env::var("SIMPLE_LINKER_DEBUG").is_ok() || options.verbose {
            match self {
                Self::Msvc => {
                    cmd.arg("/VERBOSE");
                }
                _ => {
                    cmd.arg("-v");
                }
            }
        }
    }

    /// Extract undefined symbol name from linker error message.
    fn extract_undefined_symbol(stderr: &str) -> Option<String> {
        // Common patterns:
        // GNU:  "undefined reference to `symbol'"
        // LLD:  "undefined symbol: symbol"
        // MSVC: "unresolved external symbol _symbol referenced in function _main"
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
            if let Some(start) = line.find("unresolved external symbol ") {
                let rest = &line[start + 27..];
                let end = rest
                    .find(" referenced in")
                    .or_else(|| rest.find(|c: char| c.is_whitespace()))
                    .unwrap_or(rest.len());
                return Some(rest[..end].to_string());
            }
        }
        None
    }

    /// Extract multiply-defined symbol name from linker error message.
    fn extract_multiple_definition(stderr: &str) -> Option<String> {
        // Common patterns:
        // GNU:  "multiple definition of `symbol'"
        // LLD:  "duplicate symbol: symbol"
        // MSVC: "symbol already defined in file.obj"
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
            // MSVC: "foo.obj : error LNK2005: _symbol already defined in bar.obj"
            if let Some(start) = line.find("already defined in") {
                // Symbol is before "already defined in", after the last space before it
                let prefix = &line[..start].trim_end();
                if let Some(sym_start) = prefix.rfind(' ') {
                    let sym = &prefix[sym_start + 1..];
                    if !sym.is_empty() {
                        return Some(sym.to_string());
                    }
                }
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
    /// Custom entry point symbol (None = linker default/_start).
    pub entry_point: Option<String>,
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

    /// Set entry point symbol.
    pub fn entry(mut self, sym: impl Into<String>) -> Self {
        self.entry_point = Some(sym.into());
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
        assert_eq!(NativeLinker::from_name("lld-link"), Some(NativeLinker::Lld));
        assert_eq!(NativeLinker::from_name("ld"), Some(NativeLinker::Ld));
        assert_eq!(NativeLinker::from_name("gnu"), Some(NativeLinker::Ld));
        assert_eq!(NativeLinker::from_name("msvc"), Some(NativeLinker::Msvc));
        assert_eq!(NativeLinker::from_name("link"), Some(NativeLinker::Msvc));
        assert_eq!(NativeLinker::from_name("link.exe"), Some(NativeLinker::Msvc));
        assert_eq!(NativeLinker::from_name("unknown"), None);
    }

    #[test]
    fn test_linker_command() {
        assert_eq!(NativeLinker::Mold.command(), "mold");
        #[cfg(not(target_os = "windows"))]
        assert_eq!(NativeLinker::Lld.command(), "ld.lld");
        #[cfg(target_os = "windows")]
        assert_eq!(NativeLinker::Lld.command(), "lld-link");
        assert_eq!(NativeLinker::Ld.command(), "ld");
        assert_eq!(NativeLinker::Msvc.command(), "link.exe");
    }

    #[test]
    fn test_linker_command_for_target() {
        use simple_common::target::{TargetArch, TargetOS};

        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);

        assert_eq!(NativeLinker::Lld.command_for_target(&linux), "ld.lld");
        assert_eq!(NativeLinker::Lld.command_for_target(&windows), "lld-link");
    }

    #[test]
    fn test_linker_name() {
        assert_eq!(NativeLinker::Mold.name(), "mold");
        assert_eq!(NativeLinker::Lld.name(), "lld");
        assert_eq!(NativeLinker::Ld.name(), "GNU ld");
        assert_eq!(NativeLinker::Msvc.name(), "MSVC link.exe");
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
    fn test_detect_for_target() {
        use simple_common::target::{TargetArch, TargetOS};

        // Should not panic regardless of available linkers
        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let _linker = NativeLinker::detect_for_target(&linux);

        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);
        let _linker = NativeLinker::detect_for_target(&windows);

        let macos = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        let _linker = NativeLinker::detect_for_target(&macos);
    }

    #[test]
    fn test_extract_undefined_symbol() {
        // GNU ld pattern
        let stderr = "ld: error: undefined reference to `missing_func'\n";
        assert_eq!(
            NativeLinker::extract_undefined_symbol(stderr),
            Some("missing_func".to_string())
        );

        // LLD pattern
        let stderr2 = "error: undefined symbol: other_func\n";
        assert_eq!(
            NativeLinker::extract_undefined_symbol(stderr2),
            Some("other_func".to_string())
        );

        // MSVC pattern
        let stderr3 = "main.obj : error LNK2019: unresolved external symbol _foo referenced in function _main\n";
        assert_eq!(
            NativeLinker::extract_undefined_symbol(stderr3),
            Some("_foo".to_string())
        );
    }

    #[test]
    fn test_extract_multiple_definition() {
        // GNU ld pattern
        let stderr = "ld: error: multiple definition of `duplicate_sym'\n";
        assert_eq!(
            NativeLinker::extract_multiple_definition(stderr),
            Some("duplicate_sym".to_string())
        );

        // LLD pattern
        let stderr2 = "error: duplicate symbol: other_sym\n";
        assert_eq!(
            NativeLinker::extract_multiple_definition(stderr2),
            Some("other_sym".to_string())
        );

        // MSVC pattern
        let stderr3 = "foo.obj : error LNK2005: _bar already defined in baz.obj\n";
        assert_eq!(
            NativeLinker::extract_multiple_definition(stderr3),
            Some("_bar".to_string())
        );
    }
}
