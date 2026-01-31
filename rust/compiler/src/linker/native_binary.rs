//! Native binary builder for standalone executables.
//!
//! This module provides functionality to compile Simple programs to standalone
//! native executables (ELF on Linux, PE on Windows) that can run without the
//! Simple runtime.
//!
//! # Features
//!
//! - **Standalone executables**: No runtime dependency required
//! - **4KB page locality**: Optimized code layout for fast startup
//! - **Runtime bundling**: GC, actors, and FFI functions linked statically
//! - **Cross-compilation**: Build for different target architectures
//!
//! # Usage
//!
//! ```no_run
//! use simple_compiler::linker::NativeBinaryBuilder;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let object_code = vec![]; // Object code from compilation
//! let result = NativeBinaryBuilder::new(object_code)
//!     .output("app")
//!     .layout_optimize(true)
//!     .build()?;
//! # Ok(())
//! # }
//! ```

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use simple_common::target::Target;

use super::builder::LinkerBuilder;
use super::error::{LinkerError, LinkerResult};
use super::layout::{LayoutOptimizer, LayoutSegment};
use super::native::NativeLinker;

/// Options for native binary compilation.
#[derive(Debug, Clone)]
pub struct NativeBinaryOptions {
    /// Output file path.
    pub output: PathBuf,
    /// Target architecture.
    pub target: Target,
    /// Enable 4KB page layout optimization.
    pub layout_optimize: bool,
    /// Profile data for guided layout.
    pub layout_profile: Option<PathBuf>,
    /// Strip symbols from output.
    pub strip: bool,
    /// Create position-independent executable.
    pub pie: bool,
    /// Create shared library instead of executable.
    pub shared: bool,
    /// Additional libraries to link.
    pub libraries: Vec<String>,
    /// Library search paths.
    pub library_paths: Vec<PathBuf>,
    /// Selected linker (auto-detect if None).
    pub linker: Option<NativeLinker>,
    /// Generate map file.
    pub generate_map: bool,
    /// Verbose output.
    pub verbose: bool,
}

impl Default for NativeBinaryOptions {
    fn default() -> Self {
        // Detect standard library paths for the current system
        let mut library_paths = Self::detect_system_library_paths();

        // Add Simple runtime library path from cargo target directory
        if let Some(runtime_path) = Self::find_runtime_library_path() {
            library_paths.insert(0, runtime_path);
        } else {
            // Fallback: try current working directory + target/debug
            let cwd_debug = std::env::current_dir().ok().map(|p| p.join("target/debug"));
            if let Some(path) = cwd_debug {
                if path.join("libsimple_runtime.a").exists() {
                    library_paths.insert(0, path);
                }
            }
        }

        Self {
            output: PathBuf::from("a.out"),
            target: Target::host(),
            layout_optimize: false,
            layout_profile: None,
            strip: false,
            pie: true, // Default to PIE for security (codegen generates PIC)
            shared: false,
            // Link system libraries and Simple runtime
            // pthread, dl, m, gcc_s are commonly needed by Rust code on Linux
            // gcc_s provides _Unwind_Resume for exception handling
            // simple_compiler provides Cranelift FFI and other runtime functions
            #[cfg(target_os = "linux")]
            libraries: vec![
                "c".to_string(),
                "pthread".to_string(),
                "dl".to_string(),
                "m".to_string(),
                "gcc_s".to_string(), // Unwinding support
                "simple_compiler".to_string(), // Runtime FFI functions
            ],
            #[cfg(not(target_os = "linux"))]
            libraries: vec!["c".to_string()],
            library_paths,
            linker: None,
            generate_map: false,
            verbose: false,
        }
    }
}

impl NativeBinaryOptions {
    /// Detect standard library paths for the target system.
    fn detect_system_library_paths() -> Vec<PathBuf> {
        Self::detect_library_paths_for_target(&Target::host())
    }

    /// Detect library paths for a specific target.
    pub fn detect_library_paths_for_target(target: &Target) -> Vec<PathBuf> {
        use simple_common::target::TargetArch;
        let mut paths = Vec::new();

        #[cfg(target_os = "linux")]
        {
            // Choose paths based on target architecture
            let arch_dirs: &[&str] = match target.arch {
                TargetArch::X86_64 => &[
                    "/lib/x86_64-linux-gnu",
                    "/usr/lib/x86_64-linux-gnu",
                    "/lib64",
                    "/usr/lib64",
                    // GCC runtime library paths
                    "/usr/lib/gcc/x86_64-linux-gnu/13",
                    "/usr/lib/gcc/x86_64-linux-gnu/12",
                    "/usr/lib/gcc/x86_64-linux-gnu/11",
                ],
                TargetArch::Aarch64 => &[
                    "/lib/aarch64-linux-gnu",
                    "/usr/lib/aarch64-linux-gnu",
                    "/usr/aarch64-linux-gnu/lib",
                ],
                TargetArch::Riscv64 => &[
                    "/lib/riscv64-linux-gnu",
                    "/usr/lib/riscv64-linux-gnu",
                    "/usr/riscv64-linux-gnu/lib",
                ],
                _ => &[],
            };

            for path in arch_dirs {
                let p = PathBuf::from(path);
                if p.exists() {
                    paths.push(p);
                }
            }

            // Add generic paths
            for path in ["/lib", "/usr/lib"] {
                let p = PathBuf::from(path);
                if p.exists() {
                    paths.push(p);
                }
            }
        }

        // macOS library paths
        #[cfg(target_os = "macos")]
        {
            let candidates = ["/usr/lib", "/usr/local/lib"];

            for path in candidates {
                let p = PathBuf::from(path);
                if p.exists() {
                    paths.push(p);
                }
            }
        }

        paths
    }

    /// Find the Simple runtime library path.
    ///
    /// Looks for libsimple_runtime.a in:
    /// 1. SIMPLE_RUNTIME_PATH environment variable
    /// 2. Adjacent to the current executable (for installed binaries)
    /// 3. Cargo target directory (for development)
    pub fn find_runtime_library_path() -> Option<PathBuf> {
        // Check environment variable first
        if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
            let p = PathBuf::from(&path);
            if p.exists() {
                return Some(p);
            }
        }

        // Check adjacent to current executable (e.g., /usr/lib/simple/)
        if let Ok(exe_path) = std::env::current_exe() {
            if let Some(exe_dir) = exe_path.parent() {
                // Check ../lib relative to executable
                let lib_dir = exe_dir.join("../lib");
                if lib_dir.join("libsimple_runtime.a").exists() {
                    return lib_dir.canonicalize().ok();
                }

                // Check same directory as executable
                if exe_dir.join("libsimple_runtime.a").exists() {
                    return Some(exe_dir.to_path_buf());
                }
            }
        }

        // Check cargo target directory (for development)
        // Try both release and debug directories
        let cargo_target_paths = [
            // Standard cargo target directory
            "target/release",
            "target/debug",
            // Workspace root (when running from subdirectory)
            "../target/release",
            "../target/debug",
            "../../target/release",
            "../../target/debug",
        ];

        for path in cargo_target_paths {
            let p = PathBuf::from(path);
            if p.join("libsimple_runtime.a").exists() {
                return p.canonicalize().ok();
            }
        }

        // Try to find from CARGO_MANIFEST_DIR (set during cargo build)
        if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
            let workspace_root = PathBuf::from(&manifest_dir)
                .ancestors()
                .nth(1) // Go up from rust/compiler to rust/ (Cargo workspace root)
                .map(|p| p.to_path_buf());

            if let Some(root) = workspace_root {
                for profile in ["release", "debug"] {
                    let lib_path = root.join("target").join(profile);
                    if lib_path.join("libsimple_runtime.a").exists() {
                        return Some(lib_path);
                    }
                }
            }
        }

        None
    }

    /// Create new options with default values.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set output path.
    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.output = path.into();
        self
    }

    // Use macros for common builder methods
    impl_target_method!(direct);
    impl_layout_methods!(direct);
    impl_bool_flag_methods!(direct);
    impl_linker_builder_methods!(direct);
    impl_linker_method!(direct);
}

/// Builder for native binaries.
#[derive(Debug)]
pub struct NativeBinaryBuilder {
    /// Object code from compilation.
    object_code: Vec<u8>,
    /// Build options.
    options: NativeBinaryOptions,
    /// Layout optimizer.
    layout_optimizer: Option<LayoutOptimizer>,
}

impl NativeBinaryBuilder {
    /// Create a new native binary builder with object code.
    pub fn new(object_code: Vec<u8>) -> Self {
        Self {
            object_code,
            options: NativeBinaryOptions::default(),
            layout_optimizer: None,
        }
    }

    /// Set output path.
    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.options.output = path.into();
        self
    }

    // Use macros for common builder methods (delegating to self.options)
    impl_target_method!(options);
    impl_layout_methods!(options);
    impl_bool_flag_methods!(options);
    impl_linker_builder_methods!(options);
    impl_linker_method!(options);

    /// Set custom options.
    pub fn options(mut self, options: NativeBinaryOptions) -> Self {
        self.options = options;
        self
    }

    /// Set layout optimizer.
    pub fn with_layout_optimizer(mut self, optimizer: LayoutOptimizer) -> Self {
        self.layout_optimizer = Some(optimizer);
        self
    }

    /// Build the native binary.
    pub fn build(self) -> LinkerResult<NativeBinaryResult> {
        // Create temporary directory for intermediate files
        let temp_dir =
            tempfile::tempdir().map_err(|e| LinkerError::LinkFailed(format!("failed to create temp dir: {}", e)))?;

        // Write object file
        let obj_path = temp_dir.path().join("main.o");
        std::fs::write(&obj_path, &self.object_code)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write object file: {}", e)))?;

        // Debug: Print symbols in object file
        if self.options.verbose || std::env::var("SIMPLE_LINKER_DEBUG").is_ok() {
            eprintln!("Object file: {}", obj_path.display());
            if let Ok(output) = Command::new("nm").arg(&obj_path).output() {
                eprintln!("Symbols in object file:");
                eprintln!("{}", String::from_utf8_lossy(&output.stdout));
            }
        }

        // Find C runtime startup files (not needed for shared libraries)
        let crt_files = if self.options.shared {
            Vec::new()
        } else {
            self.find_crt_files()?
        };

        // Apply layout optimization if enabled
        let _ordering_file = if self.options.layout_optimize {
            self.generate_ordering_file(temp_dir.path())?
        } else {
            None
        };

        // Build linker command
        // Order: crti.o, crt1.o, user objects, -lc, crtn.o
        let mut builder = LinkerBuilder::new();

        // Add CRT files in order: crti, Scrt1/crt1, then user code
        if crt_files.len() >= 2 {
            builder = builder.object(&crt_files[0]); // crti.o
            builder = builder.object(&crt_files[1]); // Scrt1.o or crt1.o
        }

        // Add user object file
        builder = builder.object(&obj_path);

        // Add Simple runtime and compiler static libraries directly (not via -l)
        // This ensures static linking even when shared library exists
        let runtime_dir = NativeBinaryOptions::find_runtime_library_path().or_else(|| {
            // Fallback: try current working directory + target/debug
            std::env::current_dir()
                .ok()
                .map(|p| p.join("target/debug"))
                .filter(|p| p.join("libsimple_runtime.a").exists())
        });

        if let Some(runtime_dir) = runtime_dir {
            // Check if we need the compiler library (for self-hosting compiler)
            let compiler_lib = runtime_dir.join("libsimple_compiler.a");
            let runtime_lib = runtime_dir.join("libsimple_runtime.a");

            if compiler_lib.exists() {
                // Link compiler library ONLY (it already includes runtime as staticlib)
                // The compiler staticlib bundles all dependencies including simple-runtime
                builder = builder.object(&compiler_lib);
            } else if runtime_lib.exists() {
                // Only runtime library (normal programs without compiler features)
                builder = builder.object(&runtime_lib);
            }
        }

        // Set output
        builder = builder.output(&self.options.output);

        // Apply options
        if let Some(linker) = self.options.linker {
            builder = builder.linker(linker);
        }

        for lib in &self.options.libraries {
            builder = builder.library(lib);
        }

        for path in &self.options.library_paths {
            builder = builder.library_path(path);
        }

        if self.options.strip {
            builder = builder.strip();
        }

        // PIE and shared are mutually exclusive
        if self.options.shared {
            builder = builder.shared();
        } else if self.options.pie {
            builder = builder.pie();
        }

        if self.options.generate_map {
            builder = builder.auto_map();
        }

        if self.options.verbose {
            builder = builder.verbose();
        }

        // Add dynamic linker flag for executables (both PIE and non-PIE)
        if !self.options.shared {
            if let Some(dynamic_linker) = self.find_dynamic_linker() {
                builder = builder.flag(format!("--dynamic-linker={}", dynamic_linker.display()));
            }

            // For non-PIE executables, explicitly pass -no-pie
            if !self.options.pie {
                builder = builder.flag("-no-pie".to_string());
            }
        }

        // Add crtn.o at the end (after libraries)
        if crt_files.len() >= 3 {
            builder = builder.object(&crt_files[2]); // crtn.o
        }

        // Execute linking
        match builder.link() {
            Ok(()) => Ok(NativeBinaryResult {
                output: self.options.output.clone(),
                size: std::fs::metadata(&self.options.output).map(|m| m.len()).unwrap_or(0),
            }),
            Err(LinkerError::LinkerFailed {
                exit_code,
                message,
                stderr,
            }) => {
                // Print detailed linker error
                eprintln!("Linker error (exit code {}): {}", exit_code, message);
                if !stderr.is_empty() {
                    eprintln!("Linker stderr:\n{}", stderr);
                }
                Err(LinkerError::LinkFailed(format!(
                    "{}: {}",
                    message,
                    stderr.lines().next().unwrap_or("")
                )))
            }
            Err(e) => Err(e),
        }
    }

    /// Find C runtime startup files on the system.
    fn find_crt_files(&self) -> LinkerResult<Vec<PathBuf>> {
        use simple_common::target::TargetArch;
        let mut crt_files = Vec::new();

        // Common locations for CRT files on Linux
        #[cfg(target_os = "linux")]
        {
            // Choose paths based on target architecture
            let candidates: Vec<&str> = match self.options.target.arch {
                TargetArch::X86_64 => vec![
                    "/usr/lib/x86_64-linux-gnu",
                    "/usr/lib64",
                    "/lib/x86_64-linux-gnu",
                    "/lib64",
                ],
                TargetArch::Aarch64 => vec![
                    "/usr/lib/aarch64-linux-gnu",
                    "/usr/aarch64-linux-gnu/lib",
                    "/lib/aarch64-linux-gnu",
                ],
                TargetArch::Riscv64 => vec![
                    "/usr/lib/riscv64-linux-gnu",
                    "/usr/riscv64-linux-gnu/lib",
                    "/lib/riscv64-linux-gnu",
                ],
                _ => vec!["/usr/lib"],
            };

            for dir in candidates {
                let dir_path = PathBuf::from(dir);

                // Check for Scrt1.o (for PIE) or crt1.o (for non-PIE)
                let crt1 = if self.options.pie && !self.options.shared {
                    dir_path.join("Scrt1.o")
                } else {
                    dir_path.join("crt1.o")
                };

                let crti = dir_path.join("crti.o");
                let crtn = dir_path.join("crtn.o");

                if crt1.exists() && crti.exists() && crtn.exists() {
                    crt_files.push(crti);
                    crt_files.push(crt1);
                    // crtn goes at the end, we'll add it later
                    crt_files.push(crtn);
                    break;
                }
            }
        }

        if crt_files.is_empty() {
            // Provide a more helpful error message for cross-compilation
            let arch_name = format!("{:?}", self.options.target.arch).to_lowercase();
            return Err(LinkerError::LinkFailed(format!(
                "could not find C runtime startup files for {} (crt1.o, crti.o, crtn.o). \
                 For cross-compilation, install the cross-toolchain (e.g., gcc-{}-linux-gnu)",
                arch_name, arch_name
            )));
        }

        Ok(crt_files)
    }

    /// Find the dynamic linker path for the target system.
    fn find_dynamic_linker(&self) -> Option<PathBuf> {
        use simple_common::target::TargetArch;

        #[cfg(target_os = "linux")]
        {
            let candidates: Vec<&str> = match self.options.target.arch {
                TargetArch::X86_64 => vec![
                    "/lib64/ld-linux-x86-64.so.2",
                    "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
                    "/lib/ld-linux-x86-64.so.2",
                ],
                TargetArch::Aarch64 => vec![
                    "/lib/ld-linux-aarch64.so.1",
                    "/lib/aarch64-linux-gnu/ld-linux-aarch64.so.1",
                ],
                TargetArch::Riscv64 => vec![
                    "/lib/ld-linux-riscv64-lp64d.so.1",
                    "/lib/riscv64-linux-gnu/ld-linux-riscv64-lp64d.so.1",
                ],
                _ => vec![],
            };

            for path in candidates {
                let p = PathBuf::from(path);
                if p.exists() {
                    return Some(p);
                }
            }

            // For cross-compilation, return the expected path even if it doesn't exist locally
            // (it will exist on the target system)
            if self.options.target.arch != TargetArch::host() {
                return match self.options.target.arch {
                    TargetArch::X86_64 => Some(PathBuf::from("/lib64/ld-linux-x86-64.so.2")),
                    TargetArch::Aarch64 => Some(PathBuf::from("/lib/ld-linux-aarch64.so.1")),
                    TargetArch::Riscv64 => Some(PathBuf::from("/lib/ld-linux-riscv64-lp64d.so.1")),
                    _ => None,
                };
            }
        }

        None
    }

    /// Generate symbol ordering file for layout optimization.
    fn generate_ordering_file(&self, temp_dir: &Path) -> LinkerResult<Option<PathBuf>> {
        let optimizer = match &self.layout_optimizer {
            Some(opt) => opt,
            None => return Ok(None),
        };

        // Get ordered symbols
        let symbols = optimizer.get_ordered_symbols();
        if symbols.is_empty() {
            return Ok(None);
        }

        // Write ordering file
        let ordering_path = temp_dir.join("symbol_order.txt");
        let mut file = std::fs::File::create(&ordering_path)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to create ordering file: {}", e)))?;

        for symbol in symbols {
            writeln!(file, "{}", symbol)
                .map_err(|e| LinkerError::LinkFailed(format!("failed to write symbol: {}", e)))?;
        }

        Ok(Some(ordering_path))
    }
}

/// Result of native binary build.
#[derive(Debug)]
pub struct NativeBinaryResult {
    /// Path to the output file.
    pub output: PathBuf,
    /// Size of the output file in bytes.
    pub size: u64,
}

/// Compile Simple source to native binary.
///
/// This is a convenience function that combines compilation and linking.
pub fn compile_to_native_binary(
    source: &str,
    output: impl Into<PathBuf>,
    options: Option<NativeBinaryOptions>,
) -> LinkerResult<NativeBinaryResult> {
    use crate::codegen::Codegen;
    use crate::hir;
    use crate::mir;

    let output = output.into();
    let options = options.unwrap_or_else(|| NativeBinaryOptions::default().output(&output));

    // Parse source
    let mut parser = simple_parser::Parser::new(source);
    let ast_module = parser
        .parse()
        .map_err(|e| LinkerError::LinkFailed(format!("parse error: {}", e)))?;

    // Lower to HIR
    let hir_module =
        hir::lower(&ast_module).map_err(|e| LinkerError::LinkFailed(format!("HIR lowering error: {}", e)))?;

    // Lower to MIR
    let mir_module =
        mir::lower_to_mir(&hir_module).map_err(|e| LinkerError::LinkFailed(format!("MIR lowering error: {}", e)))?;

    // Generate object code
    let codegen = Codegen::for_target(options.target.clone())
        .map_err(|e| LinkerError::LinkFailed(format!("codegen error: {}", e)))?;
    let object_code = codegen
        .compile_module(&mir_module)
        .map_err(|e| LinkerError::LinkFailed(format!("compilation error: {}", e)))?;

    // Build native binary
    let mut builder = NativeBinaryBuilder::new(object_code).options(options);

    // Set up layout optimizer if requested
    if builder.options.layout_optimize {
        let optimizer = LayoutOptimizer::new();
        builder = builder.with_layout_optimizer(optimizer);
    }

    builder.build()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_options_default() {
        let options = NativeBinaryOptions::default();
        assert!(options.pie);
        assert!(!options.strip);
        assert!(!options.shared);
        assert!(options.libraries.contains(&"c".to_string()));
    }

    #[test]
    fn test_options_builder() {
        let options = NativeBinaryOptions::new()
            .output("test")
            .strip(true)
            .pie(false)
            .library("m")
            .verbose(true);

        assert_eq!(options.output, PathBuf::from("test"));
        assert!(options.strip);
        assert!(!options.pie);
        assert!(options.libraries.contains(&"m".to_string()));
        assert!(options.verbose);
    }

    #[test]
    fn test_builder_creation() {
        let builder = NativeBinaryBuilder::new(vec![1, 2, 3, 4]).output("test").strip(true);

        assert_eq!(builder.options.output, PathBuf::from("test"));
        assert!(builder.options.strip);
    }

    // ============================================================================
    // Phase 3: Additional Comprehensive Tests for Linker Module
    // ============================================================================

    #[test]
    fn test_library_path_detection() {
        // Test that system library paths are detected
        let paths = NativeBinaryOptions::detect_system_library_paths();

        // Should find at least some standard library paths on Unix systems
        #[cfg(target_family = "unix")]
        {
            assert!(
                !paths.is_empty(),
                "Should detect at least one system library path"
            );
        }
    }

    #[test]
    fn test_find_runtime_library() {
        // Test runtime library detection (may return None in some build configs)
        let runtime_path = NativeBinaryOptions::find_runtime_library_path();

        if let Some(path) = runtime_path {
            // If found, should be a valid directory
            assert!(
                path.is_dir() || path.parent().map(|p| p.is_dir()).unwrap_or(false),
                "Runtime path should be a directory: {:?}",
                path
            );
        }
    }

    // Note: CRT file detection is done by NativeBinaryBuilder.find_crt_files()
    // which is a private method, so we can't test it directly.
    // Integration tests will cover this functionality.

    #[test]
    fn test_options_with_multiple_libraries() {
        let options = NativeBinaryOptions::new()
            .library("pthread")
            .library("dl")
            .library("m");

        // Note: .library() adds to existing libraries (which include defaults)
        assert!(options.libraries.contains(&"pthread".to_string()));
        assert!(options.libraries.contains(&"dl".to_string()));
        assert!(options.libraries.contains(&"m".to_string()));
    }

    #[test]
    fn test_options_with_library_paths() {
        let path1 = PathBuf::from("/usr/lib");
        let path2 = PathBuf::from("/usr/local/lib");

        let options = NativeBinaryOptions::new()
            .library_path(path1.clone())
            .library_path(path2.clone());

        // Note: .library_path() adds to existing paths (which may include defaults)
        assert!(options.library_paths.contains(&path1));
        assert!(options.library_paths.contains(&path2));
    }

    #[test]
    fn test_shared_library_mode() {
        let options = NativeBinaryOptions::new().shared(true).pie(false);

        assert!(options.shared);
        assert!(!options.pie); // Shared libs typically don't use PIE
    }

    #[test]
    fn test_layout_optimization_enabled() {
        let options = NativeBinaryOptions::new().layout_optimize(true);

        assert!(options.layout_optimize);
    }

    #[test]
    fn test_layout_profile_path() {
        let profile_path = PathBuf::from("/tmp/profile.data");
        let options = NativeBinaryOptions::new().layout_profile(profile_path.clone());

        assert_eq!(options.layout_profile, Some(profile_path));
    }

    #[test]
    fn test_map_file_generation() {
        let options = NativeBinaryOptions::new().map(true);

        assert!(options.generate_map);
    }

    #[test]
    fn test_verbose_mode() {
        let options = NativeBinaryOptions::new().verbose(true);

        assert!(options.verbose);
    }

    #[test]
    fn test_target_architecture() {
        let options = NativeBinaryOptions::new().target(Target::host());

        assert_eq!(options.target, Target::host());
    }

    #[test]
    fn test_default_options_has_libc() {
        let options = NativeBinaryOptions::default();

        #[cfg(target_os = "linux")]
        {
            assert!(
                options.libraries.contains(&"c".to_string()),
                "Default options should include libc"
            );
        }
    }

    #[test]
    fn test_builder_chaining() {
        let builder = NativeBinaryBuilder::new(vec![])
            .output("myapp")
            .strip(true)
            .pie(false)
            .library("pthread")
            .verbose(true);

        assert_eq!(builder.options.output, PathBuf::from("myapp"));
        assert!(builder.options.strip);
        assert!(!builder.options.pie);
        assert!(builder.options.libraries.contains(&"pthread".to_string()));
        assert!(builder.options.verbose);
    }

    #[test]
    fn test_builder_with_layout_optimizer() {
        let optimizer = LayoutOptimizer::new();
        let builder = NativeBinaryBuilder::new(vec![]).with_layout_optimizer(optimizer);

        assert!(builder.layout_optimizer.is_some());
    }

    #[test]
    fn test_builder_options_method() {
        let options = NativeBinaryOptions::new().strip(true).pie(false);
        let builder = NativeBinaryBuilder::new(vec![]).options(options.clone());

        assert_eq!(builder.options.strip, options.strip);
        assert_eq!(builder.options.pie, options.pie);
    }

    #[test]
    fn test_empty_object_code() {
        let builder = NativeBinaryBuilder::new(vec![]);

        assert!(builder.object_code.is_empty());
    }

    #[test]
    fn test_non_empty_object_code() {
        let code = vec![0x7f, 0x45, 0x4c, 0x46]; // ELF magic number
        let builder = NativeBinaryBuilder::new(code.clone());

        assert_eq!(builder.object_code, code);
    }

    #[test]
    fn test_output_path_relative() {
        let options = NativeBinaryOptions::new().output("bin/myapp");

        assert_eq!(options.output, PathBuf::from("bin/myapp"));
    }

    #[test]
    fn test_output_path_absolute() {
        let options = NativeBinaryOptions::new().output("/usr/local/bin/myapp");

        assert_eq!(options.output, PathBuf::from("/usr/local/bin/myapp"));
    }
}
