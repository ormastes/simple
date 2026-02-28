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

use simple_common::target::{LinkerFlavor, Target, TargetArch, TargetOS};

use super::builder::LinkerBuilder;
use super::error::{LinkerError, LinkerResult};
use super::layout::{LayoutOptimizer, LayoutSegment};
use super::native::NativeLinker;

/// Get the architecture-appropriate `ret` instruction for inline asm stubs.
fn asm_ret_instruction(target: &Target) -> &'static str {
    match target.arch {
        TargetArch::X86_64 | TargetArch::X86 => "ret",
        TargetArch::Aarch64 => "ret", // uses x30 (link register)
        TargetArch::Arm => "bx lr",
        TargetArch::Riscv64 | TargetArch::Riscv32 => "ret", // pseudo for jalr x0, ra, 0
        _ => "ret", // fallback
    }
}

/// Detect the C compiler for the target platform.
///
/// On Windows, defaults to `cl.exe`. Respects the `CC` environment variable.
fn detect_c_compiler(target: &Target) -> String {
    if let Ok(cc) = std::env::var("CC") {
        return cc;
    }
    match target.os {
        TargetOS::Windows => "cl.exe".to_string(),
        _ => "cc".to_string(),
    }
}

/// Build arguments for compiling a C file to an object file.
///
/// Returns (args_before_output, output_flag, args_after_output) based on compiler type.
/// MSVC uses `/c /Fo<out>`, GNU uses `-c -o <out>`.
fn compile_c_args(cc: &str, output: &Path, input: &Path) -> Vec<String> {
    if is_msvc_compiler(cc) {
        vec![
            "/c".to_string(),
            format!("/Fo{}", output.display()),
            input.display().to_string(),
        ]
    } else {
        vec![
            "-c".to_string(),
            "-o".to_string(),
            output.display().to_string(),
            input.display().to_string(),
        ]
    }
}

/// Check if a compiler name looks like MSVC cl.exe.
fn is_msvc_compiler(cc: &str) -> bool {
    let base = std::path::Path::new(cc)
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(cc);
    base.eq_ignore_ascii_case("cl") || base.eq_ignore_ascii_case("cl.exe")
}

/// Detect the symbol listing tool for the target platform.
///
/// Returns the command and arguments for listing undefined symbols.
/// - Unix: `nm -u`
/// - Windows: tries `dumpbin /SYMBOLS` > `llvm-nm -u` > `nm -u`
fn detect_nm_command(target: &Target) -> (String, Vec<String>) {
    if target.os == TargetOS::Windows {
        // Try dumpbin first (MSVC tool)
        if Command::new("dumpbin").arg("/?").output().map(|o| o.status.success()).unwrap_or(false) {
            return ("dumpbin".to_string(), vec!["/SYMBOLS".to_string()]);
        }
        // Try llvm-nm
        if Command::new("llvm-nm").arg("--version").output().map(|o| o.status.success()).unwrap_or(false) {
            return ("llvm-nm".to_string(), vec!["-u".to_string()]);
        }
    }
    ("nm".to_string(), vec!["-u".to_string()])
}

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

        // Add Simple compiler static library path so -lsimple_compiler resolves
        if let Some(compiler_path) = Self::find_compiler_library_path() {
            if !library_paths.contains(&compiler_path) {
                library_paths.insert(0, compiler_path);
            }
        }

        let target = Target::host();
        let libraries = Self::default_libraries_for_target(&target);

        Self {
            output: PathBuf::from("a.out"),
            target,
            layout_optimize: false,
            layout_profile: None,
            strip: false,
            pie: true, // Default to PIE for security (codegen generates PIC)
            shared: false,
            libraries,
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

    /// Get default libraries for a specific target OS.
    pub fn default_libraries_for_target(target: &Target) -> Vec<String> {
        use simple_common::target::TargetOS;
        match target.os {
            TargetOS::Linux => vec![
                "c".into(),
                "pthread".into(),
                "dl".into(),
                "m".into(),
                "gcc_s".into(),          // Unwinding support
                "lzma".into(),           // Needed by xz2 (dependency chain)
                "simple_runtime".into(), // Runtime FFI functions
            ],
            TargetOS::MacOS => vec![
                "c".into(),
                "System".into(),         // Provides pthread, dl, m on macOS
                "simple_runtime".into(),
            ],
            TargetOS::Windows => vec![
                "c".into(),
                "msvcrt".into(),
                "kernel32".into(),
                "ws2_32".into(),
                "advapi32".into(),
                "simple_runtime".into(),
            ],
            TargetOS::FreeBSD => vec![
                "c".into(),
                "pthread".into(),
                "m".into(),
                "execinfo".into(),
                "simple_runtime".into(),
            ],
            _ => vec!["c".into()],
        }
    }

    /// Detect library paths for a specific target.
    pub fn detect_library_paths_for_target(target: &Target) -> Vec<PathBuf> {
        use simple_common::target::{TargetArch, TargetOS};
        let mut paths = Vec::new();

        match target.os {
            TargetOS::Linux => {
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
            TargetOS::MacOS => {
                for path in ["/usr/lib", "/usr/local/lib"] {
                    let p = PathBuf::from(path);
                    if p.exists() {
                        paths.push(p);
                    }
                }
            }
            TargetOS::FreeBSD => {
                for path in ["/usr/lib", "/usr/local/lib"] {
                    let p = PathBuf::from(path);
                    if p.exists() {
                        paths.push(p);
                    }
                }
            }
            TargetOS::Windows => {
                // Probe Windows SDK and MSVC lib paths from environment
                let arch_subdir = match target.arch {
                    TargetArch::X86_64 => "x64",
                    TargetArch::Aarch64 => "arm64",
                    TargetArch::X86 => "x86",
                    TargetArch::Arm => "arm",
                    _ => "x64",
                };

                // Windows SDK (UniversalCRTSdkDir / WindowsSdkDir)
                for env_var in ["UniversalCRTSdkDir", "WindowsSdkDir"] {
                    if let Ok(sdk_dir) = std::env::var(env_var) {
                        // Try versioned paths: Lib/<version>/um/<arch> and Lib/<version>/ucrt/<arch>
                        if let Ok(version) = std::env::var("WindowsSDKVersion") {
                            let version = version.trim_end_matches('\\');
                            for subdir in ["um", "ucrt"] {
                                let p = PathBuf::from(&sdk_dir).join("Lib").join(version).join(subdir).join(arch_subdir);
                                if p.exists() {
                                    paths.push(p);
                                }
                            }
                        }
                    }
                }

                // MSVC toolset (VCToolsInstallDir or VCINSTALLDIR)
                for env_var in ["VCToolsInstallDir", "VCINSTALLDIR"] {
                    if let Ok(vc_dir) = std::env::var(env_var) {
                        let p = PathBuf::from(&vc_dir).join("lib").join(arch_subdir);
                        if p.exists() {
                            paths.push(p);
                        }
                    }
                }
            }
            _ => {}
        }

        paths
    }

    /// Get the platform-appropriate static library filename for a base name.
    ///
    /// Returns `lib{base}.a` on Unix (Linux, macOS, FreeBSD) and `{base}.lib` on Windows.
    pub fn static_lib_name(base: &str, target: &Target) -> String {
        use simple_common::target::TargetOS;
        match target.os {
            TargetOS::Windows => format!("{}.lib", base),
            _ => format!("lib{}.a", base),
        }
    }

    /// Find the Simple runtime library path.
    ///
    /// Looks for libsimple_runtime.a (or simple_runtime.lib on Windows) in:
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

    /// Find the Simple compiler static library path (libsimple_compiler.a).
    ///
    /// Checks the same locations as runtime detection plus current/parent target dirs.
    pub fn find_compiler_library_path() -> Option<PathBuf> {
        // Check env override
        if let Ok(path) = std::env::var("SIMPLE_COMPILER_PATH") {
            let p = PathBuf::from(&path);
            if p.exists() {
                return Some(p);
            }
        }

        // Check current executable directory and ../lib
        if let Ok(exe_path) = std::env::current_exe() {
            if let Some(exe_dir) = exe_path.parent() {
                let lib_dir = exe_dir.join("../lib");
                if lib_dir.join("libsimple_compiler.a").exists() {
                    return lib_dir.canonicalize().ok();
                }
                if exe_dir.join("libsimple_compiler.a").exists() {
                    return Some(exe_dir.to_path_buf());
                }
            }
        }

        // Check common cargo target locations
        let cargo_target_paths = [
            "target/release",
            "target/debug",
            "../target/release",
            "../target/debug",
            "../../target/release",
            "../../target/debug",
        ];

        for path in cargo_target_paths {
            let p = PathBuf::from(path);
            if p.join("libsimple_compiler.a").exists() {
                return p.canonicalize().ok();
            }
        }

        // Check workspace root from manifest dir
        if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
            let workspace_root = PathBuf::from(&manifest_dir).ancestors().nth(1).map(|p| p.to_path_buf());

            if let Some(root) = workspace_root {
                for profile in ["release", "debug"] {
                    let lib_path = root.join("target").join(profile);
                    if lib_path.join("libsimple_compiler.a").exists() {
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
        let (temp_path, _temp_guard) = if std::env::var("SIMPLE_KEEP_TEMP").is_ok() {
            let path = temp_dir.into_path();
            eprintln!("SIMPLE_KEEP_TEMP=1: keeping temp objects in {}", path.display());
            (path, None)
        } else {
            (temp_dir.path().to_path_buf(), Some(temp_dir))
        };

        // Write object file
        let obj_path = temp_path.join("main.o");
        std::fs::write(&obj_path, &self.object_code)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write object file: {}", e)))?;

        // Bootstrap helpers: stubs for entry + missing runtime symbols.
        let mut bootstrap_stubs: Vec<PathBuf> = Vec::new();
        let bootstrap_mode = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
        let mut require_crypto = false;
        let ret_insn = asm_ret_instruction(&self.options.target);

        if bootstrap_mode {
            let cc = detect_c_compiler(&self.options.target);

            // 1) main shim
            let stub_c = temp_path.join("_bootstrap_main.c");
            let stub_o = temp_path.join("_bootstrap_main.o");
            std::fs::write(
                &stub_c,
                r#"
extern int spl_main(void);
int main(int argc, char** argv) {
    (void)argc; (void)argv;
    int r = spl_main ? spl_main() : 0;
    return r;
}
"#,
            )
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write stub: {}", e)))?;
            let status = std::process::Command::new(&cc)
                .args(compile_c_args(&cc, &stub_o, &stub_c))
                .status()
                .map_err(|e| LinkerError::LinkFailed(format!("failed to compile stub: {}", e)))?;
            if status.success() {
                bootstrap_stubs.push(stub_o);
            } else {
                eprintln!(
                    "warning: failed to build bootstrap main stub with {} (status {})",
                    cc, status
                );
            }

            // 2) common missing-symbol stub
            let miss_c = temp_path.join("_bootstrap_missing.c");
            let miss_o = temp_path.join("_bootstrap_missing.o");
            std::fs::write(
                &miss_c,
                format!(r#"
#include <stdint.h>
#include <stdbool.h>
__attribute__((weak)) int64_t get_global_GLOBAL_LOG_LEVEL(void) {{ return 0; }}
__attribute__((weak)) void set_global_GLOBAL_LOG_LEVEL(int64_t v) {{ (void)v; }}
__attribute__((weak)) bool rt_file_rename(const char* a, const char* b) {{ (void)a; (void)b; return true; }}
__attribute__((weak)) void rt_fault_set_stack_overflow_detection(int64_t v) {{ (void)v; }}
__attribute__((weak)) void rt_fault_set_timeout(int64_t v) {{ (void)v; }}
__attribute__((weak)) void rt_fault_set_execution_limit(int64_t v) {{ (void)v; }}
__attribute__((weak)) void rt_debug_set_active(int64_t v) {{ (void)v; }}
__attribute__((weak)) void rt_debug_enable(void) {{}}
__attribute__((weak)) void rt_debug_disable(void) {{}}
// Real time helpers: provide working wall-clock nanos/micros for bootstrap.
#if defined(_WIN32)
#include <windows.h>
static inline int64_t _rt_now_nanos(void) {{
    LARGE_INTEGER freq, count;
    if (!QueryPerformanceFrequency(&freq) || !QueryPerformanceCounter(&count)) return 0;
    return (int64_t)((double)count.QuadPart / (double)freq.QuadPart * 1000000000.0);
}}
#else
#include <time.h>
static inline int64_t _rt_now_nanos(void) {{
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}}
#endif
__attribute__((weak)) int64_t rt_time_now_nanos(void) {{ return _rt_now_nanos(); }}
__attribute__((weak)) int64_t rt_time_now_micros(void) {{ return _rt_now_nanos() / 1000; }}
__attribute__((weak)) int64_t rt_time_now_unix_micros(void) {{ return _rt_now_nanos() / 1000; }}
__attribute__((weak)) char* rt_hostname(void) {{ return (char*)""; }}
__attribute__((weak, visibility("default"))) void* get_global_SCOPE_LEVELS(void) {{ return 0; }}
__attribute__((weak, visibility("default"))) int64_t count_by_severity(void) {{ return 0; }}
__asm__(".weak SCOPE_LEVELS.contains_key\nSCOPE_LEVELS.contains_key:\n  {ret_insn}\n");
"#, ret_insn = ret_insn),
            )
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write missing-symbol stub: {}", e)))?;
            let status = std::process::Command::new(&cc)
                .args(compile_c_args(&cc, &miss_o, &miss_c))
                .status()
                .map_err(|e| LinkerError::LinkFailed(format!("failed to compile missing-symbol stub: {}", e)))?;
            if status.success() {
                bootstrap_stubs.push(miss_o);
            } else {
                eprintln!(
                    "warning: failed to build bootstrap missing-symbol stub with {} (status {})",
                    cc, status
                );
            }

            // 3) auto-generate stubs for a constrained set of undefined symbols.
            let (nm_cmd, nm_args) = detect_nm_command(&self.options.target);
            if let Ok(nm_out) = std::process::Command::new(&nm_cmd).args(&nm_args).arg(&obj_path).output() {
                let mut symbols = std::collections::BTreeSet::new();
                // Allowlist: core runtime hooks (rt_*), debugger (ds_*), globals, and a
                // short list of compiler/service symbols that may be pruned in bootstrap.
                let extra_keep = [
                    "BackendPort",
                    "BlockResolver",
                    "AopWeaver",
                    "CodegenPipeline",
                    "CompilerBackendImpl",
                    "DiContainer",
                    "compile_module_with_backend",
                    "Scope",
                    "ScopeId",
                    "SymbolTable",
                    "LogAspect",
                    "NativeLinkOptions",
                    "visibilitychecker_new",
                    "VisibilityWarning.new",
                    "with_resolved_blocks",
                    "write_elf_bytes_to_file",
                    "HirLowering",
                    "desugar_module",
                    "optimize_mir_module",
                    "process_async_mir",
                    "get_effective_backend_name",
                    "resolve_methods",
                    "link_to_native",
                    "link_llvm_native",
                    "link_to_smf",
                    "link_to_self_contained",
                    "run_monomorphization",
                    "run_effect_pass",
                    "run_compile",
                    "generate_cmake_for_modules",
                    "SmfHeader.new_v1_1",
                    "new",
                    "create",
                    "from_function",
                    "aggressive",
                    "eval_static_assert",
                    "int",
                    "preprocess_conditionals",
                    "load_path",
                    "join_path",
                    "is_absolute_path",
                    "for_arch",
                    "host",
                    "parse",
                    "parse_leak_dump",
                    "symbols_get",
                    "size",
                    "speed",
                    "RUNTIME_SYMBOL_NAMES.contains",
                    "checker_check_symbol_access",
                    "checker_get_warnings",
                    "checker_record_warning",
                    "simple_contract_check",
                    "simple_contract_check_msg",
                    "fallback",
                    "doctest_is_dir",
                    "doctest_is_file",
                    "doctest_path_contains",
                    "doctest_path_exists",
                    "doctest_path_has_extension",
                    "doctest_read_file",
                    "doctest_walk_directory",
                    "ffi_regex_is_match",
                    "ffi_regex_find",
                    "ffi_regex_find_all",
                    "ffi_regex_captures",
                    "ffi_regex_replace",
                    "ffi_regex_replace_all",
                    "ffi_regex_split",
                    "ffi_regex_split_n",
                    "native_http_send",
                    "native_tcp_accept",
                    "native_tcp_bind",
                    "native_tcp_close",
                    "native_tcp_connect",
                    "native_tcp_connect_timeout",
                    "native_tcp_flush",
                    "native_tcp_get_nodelay",
                    "native_tcp_peek",
                    "native_tcp_read",
                    "native_tcp_set_backlog",
                    "native_tcp_set_keepalive",
                    "native_tcp_set_nodelay",
                    "native_tcp_set_read_timeout",
                    "native_tcp_set_write_timeout",
                    "native_tcp_shutdown",
                    "native_tcp_write",
                    "native_udp_bind",
                    "native_udp_close",
                    "native_udp_connect",
                    "native_udp_get_broadcast",
                    "native_udp_get_ttl",
                    "native_udp_join_multicast_v4",
                    "native_udp_join_multicast_v6",
                    "native_udp_leave_multicast_v4",
                    "native_udp_leave_multicast_v6",
                    "native_udp_peek",
                    "native_udp_peek_from",
                    "native_udp_peer_addr",
                    "native_udp_recv",
                    "native_udp_recv_from",
                    "native_udp_send",
                    "native_udp_send_to",
                    "native_udp_set_broadcast",
                    "native_udp_set_multicast_loop",
                    "native_udp_set_multicast_ttl",
                    "native_udp_set_read_timeout",
                    "native_udp_set_ttl",
                    "native_udp_set_write_timeout",
                ];
                let rt_keep = [
                    "rt_time_now_nanos",
                    "rt_time_now_micros",
                    "rt_time_now_unix_micros",
                    "rt_file_mmap_read_text",
                    "rt_file_mmap_read_bytes",
                    "rt_file_read_text_at",
                    "rt_file_read_bytes_at",
                    "rt_file_write_text_at",
                    "rt_file_write_bytes_at",
                    "rt_mmap",
                    "rt_mmap_raw",
                    "rt_munmap",
                    "rt_munmap_raw",
                    "rt_madvise",
                    "rt_msync",
                    "rt_process_spawn_async",
                    "rt_process_wait",
                    "rt_process_is_running",
                    "rt_process_kill",
                    "rt_hostname",
                    "rt_fault_set_stack_overflow_detection",
                    "rt_fault_set_timeout",
                    "rt_fault_set_execution_limit",
                    "rt_debug_set_active",
                    "rt_debug_enable",
                    "rt_debug_disable",
                    "rt_file_rename",
                    "rt_file_write",
                    "rt_file_delete",
                    "rt_file_size",
                    "rt_file_lock",
                    "rt_file_unlock",
                    "rt_getpid",
                    "rt_compile_to_llvm_ir",
                    "rt_file_hash_sha256",
                    "rt_path_parent",
                    "range",
                ];
                for line in String::from_utf8_lossy(&nm_out.stdout).lines() {
                    if let Some(sym) = line.split_whitespace().last() {
                        let keep = sym.starts_with("ds_")
                            || sym.starts_with("get_global_")
                            || sym.starts_with("set_global_")
                            || sym.contains("GLOBAL_LOG_LEVEL")
                            || sym.contains("SCOPE_LEVELS")
                            || extra_keep.contains(&sym)
                            || rt_keep.contains(&sym);
                        if keep {
                            symbols.insert(sym.to_string());
                        }
                    }
                }

                if !symbols.is_empty() {
                    let auto_c = temp_path.join("_bootstrap_auto.c");
                    let auto_o = temp_path.join("_bootstrap_auto.o");
                    let mut code = String::from("#include <stdint.h>\n#include <stdbool.h>\n");
                    for sym in &symbols {
                        let is_data = sym.contains("GLOBAL_") || sym.contains("SCOPE_");
                        let valid_ident = sym.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') && sym != "int";
                        if is_data && valid_ident {
                            code.push_str(&format!("__attribute__((weak, used)) int64_t {0} = 0;\n", sym));
                        } else if valid_ident {
                            code.push_str(&format!(
                                "__attribute__((weak, used)) int64_t {0}(void) {{ return 0; }}\n",
                                sym
                            ));
                        } else {
                            let clean = sym.replace('\"', "");
                            code.push_str(&format!(
                                "__asm__(\".weak {0}\\n{0}:\\n  {1}\\n\");\n",
                                clean, ret_insn
                            ));
                        }
                    }
                    std::fs::write(&auto_c, code)
                        .map_err(|e| LinkerError::LinkFailed(format!("failed to write auto stub: {}", e)))?;
                    let status = std::process::Command::new(&cc)
                        .args(compile_c_args(&cc, &auto_o, &auto_c))
                        .status()
                        .map_err(|e| LinkerError::LinkFailed(format!("failed to compile auto stub: {}", e)))?;
                    if status.success() {
                        bootstrap_stubs.push(auto_o);
                    } else {
                        eprintln!("warning: failed to build auto stub with {} (status {})", cc, status);
                    }
                }
            }
        }

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
            self.generate_ordering_file(&temp_path)?
        } else {
            None
        };

        // Helper to build and execute a link with given output/flags
        let linker_flavor = self.options.target.linker_flavor();
        let mut do_link = |out_path: &Path,
                           allow_unresolved: bool,
                           extra_stubs: &[PathBuf],
                           require_crypto: bool|
         -> LinkerResult<()> {
            let mut builder = LinkerBuilder::new()
                .target(self.options.target);

            if crt_files.len() >= 2 {
                builder = builder.object(&crt_files[0]);
                builder = builder.object(&crt_files[1]);
            }

            builder = builder.object(&obj_path);

            // Whole-archive flags differ by linker flavor
            if !extra_stubs.is_empty() {
                match linker_flavor {
                    LinkerFlavor::Msvc => {
                        // MSVC: /WHOLEARCHIVE:file for each stub
                        for stub in extra_stubs {
                            builder = builder.flag(format!("/WHOLEARCHIVE:{}", stub.display()));
                        }
                    }
                    LinkerFlavor::Gnu => {
                        if matches!(self.options.target.os, TargetOS::MacOS) {
                            // macOS ld64: -force_load per archive
                            for stub in extra_stubs {
                                builder = builder.flag("-force_load".to_string());
                                builder = builder.object(stub);
                            }
                        } else {
                            // GNU ld / LLD: --whole-archive / --no-whole-archive
                            builder = builder.flag("--whole-archive");
                            for stub in extra_stubs {
                                builder = builder.object(stub);
                            }
                            builder = builder.flag("--no-whole-archive");
                        }
                    }
                    LinkerFlavor::WasmLd => {
                        builder = builder.flag("--whole-archive");
                        for stub in extra_stubs {
                            builder = builder.object(stub);
                        }
                        builder = builder.flag("--no-whole-archive");
                    }
                }
            }

            // Allow-unresolved flags differ by linker flavor
            if allow_unresolved {
                match linker_flavor {
                    LinkerFlavor::Msvc => {
                        builder = builder.flag("/FORCE:UNRESOLVED".to_string());
                    }
                    LinkerFlavor::Gnu => {
                        if matches!(self.options.target.os, TargetOS::MacOS) {
                            builder = builder.flag("-undefined".to_string());
                            builder = builder.flag("dynamic_lookup".to_string());
                        } else {
                            builder = builder.flag("--unresolved-symbols=ignore-all".to_string());
                        }
                    }
                    LinkerFlavor::WasmLd => {
                        builder = builder.flag("--allow-undefined".to_string());
                    }
                }
            }

            let runtime_dir = NativeBinaryOptions::find_runtime_library_path().or_else(|| {
                std::env::current_dir()
                    .ok()
                    .map(|p| p.join("target/debug"))
                    .filter(|p| p.join("libsimple_runtime.a").exists())
            });

            if let Some(runtime_dir) = runtime_dir {
                let native_all_lib = runtime_dir.join("libsimple_native_all.a");
                let compiler_lib = runtime_dir.join("libsimple_compiler.a");
                let runtime_lib = runtime_dir.join("libsimple_runtime.a");
                if native_all_lib.exists() {
                    builder = builder.object(&native_all_lib);
                } else if runtime_lib.exists() {
                    builder = builder.object(&runtime_lib);
                } else if compiler_lib.exists() {
                    builder = builder.object(&compiler_lib);
                }
            }

            builder = builder.output(out_path);

            if let Some(linker) = self.options.linker {
                builder = builder.linker(linker);
            }
            for lib in &self.options.libraries {
                builder = builder.library(lib);
            }
            for path in &self.options.library_paths {
                builder = builder.library_path(path);
            }
            if require_crypto {
                builder = builder.library("crypto");
            }
            if self.options.strip {
                builder = builder.strip();
            }
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

            // Dynamic linker and no-PIE flags (GNU/FreeBSD only, not macOS/Windows)
            if !self.options.shared && matches!(linker_flavor, LinkerFlavor::Gnu) {
                if !matches!(self.options.target.os, TargetOS::MacOS) {
                    if let Some(dynamic_linker) = self.find_dynamic_linker() {
                        builder = builder.flag(format!("--dynamic-linker={}", dynamic_linker.display()));
                    }
                    if !self.options.pie {
                        builder = builder.flag("-no-pie".to_string());
                    }
                }
            }

            if crt_files.len() >= 3 {
                builder = builder.object(&crt_files[2]); // crtn.o
            }

            builder.link()
        };

        // First pass: allow unresolved during bootstrap so we can see missing symbols.
        let temp_out = temp_path.join("_bootstrap_pass1");
        let first_out = if bootstrap_mode {
            &temp_out
        } else {
            Path::new(&self.options.output)
        };
        do_link(first_out, bootstrap_mode, &bootstrap_stubs, require_crypto)?;

        // If bootstrap, scan undefineds, add auto-stubs (done earlier for main.o), then relink without allow-unresolved.
            let final_result = if bootstrap_mode {
                // Regenerate auto-stubs from first-pass binary (captures runtime needs)
                let (nm_cmd2, nm_args2) = detect_nm_command(&self.options.target);
                let nm_out = std::process::Command::new(&nm_cmd2)
                    .args(&nm_args2)
                    .arg(&first_out)
                    .output()
                    .map_err(|e| LinkerError::LinkFailed(format!("failed to run {} on first-pass output: {}", nm_cmd2, e)))?;

                let mut symbols = std::collections::BTreeSet::new();
                let extra_keep = [
                    "BackendPort",
                    "BlockResolver",
                    "AopWeaver",
                    "CodegenPipeline",
                    "CompilerBackendImpl",
                    "DiContainer",
                    "compile_module_with_backend",
                    "Scope",
                    "ScopeId",
                    "SymbolTable",
                    "LogAspect",
                    "NativeLinkOptions",
                    "visibilitychecker_new",
                    "VisibilityWarning.new",
                    "with_resolved_blocks",
                    "write_elf_bytes_to_file",
                    "HirLowering",
                    "desugar_module",
                    "optimize_mir_module",
                    "process_async_mir",
                    "get_effective_backend_name",
                    "resolve_methods",
                    "link_to_native",
                    "link_llvm_native",
                    "link_to_smf",
                    "link_to_self_contained",
                    "run_monomorphization",
                    "run_effect_pass",
                    "run_compile",
                    "generate_cmake_for_modules",
                    "SmfHeader.new_v1_1",
                    "new",
                    "create",
                    "from_function",
                    "aggressive",
                    "eval_static_assert",
                    "int",
                    "preprocess_conditionals",
                    "load_path",
                    "join_path",
                    "is_absolute_path",
                    "for_arch",
                    "host",
                    "parse",
                    "parse_leak_dump",
                    "symbols_get",
                    "size",
                    "speed",
                    "RUNTIME_SYMBOL_NAMES.contains",
                    "checker_check_symbol_access",
                    "checker_get_warnings",
                    "checker_record_warning",
                    "simple_contract_check",
                    "simple_contract_check_msg",
                    "fallback",
                    "doctest_is_dir",
                    "doctest_is_file",
                    "doctest_path_contains",
                    "doctest_path_exists",
                    "doctest_path_has_extension",
                    "doctest_read_file",
                    "doctest_walk_directory",
                    "ffi_regex_is_match",
                    "ffi_regex_find",
                    "ffi_regex_find_all",
                    "ffi_regex_captures",
                    "ffi_regex_replace",
                    "ffi_regex_replace_all",
                    "ffi_regex_split",
                    "ffi_regex_split_n",
                    "native_http_send",
                    "native_tcp_accept",
                    "native_tcp_bind",
                    "native_tcp_close",
                    "native_tcp_connect",
                    "native_tcp_connect_timeout",
                    "native_tcp_flush",
                    "native_tcp_get_nodelay",
                    "native_tcp_peek",
                    "native_tcp_read",
                    "native_tcp_set_backlog",
                    "native_tcp_set_keepalive",
                    "native_tcp_set_nodelay",
                    "native_tcp_set_read_timeout",
                    "native_tcp_set_write_timeout",
                    "native_tcp_shutdown",
                    "native_tcp_write",
                    "native_udp_bind",
                    "native_udp_close",
                    "native_udp_connect",
                    "native_udp_get_broadcast",
                    "native_udp_get_ttl",
                    "native_udp_join_multicast_v4",
                    "native_udp_join_multicast_v6",
                    "native_udp_leave_multicast_v4",
                    "native_udp_leave_multicast_v6",
                    "native_udp_peek",
                    "native_udp_peek_from",
                    "native_udp_peer_addr",
                    "native_udp_recv",
                    "native_udp_recv_from",
                    "native_udp_send",
                    "native_udp_send_to",
                    "native_udp_set_broadcast",
                    "native_udp_set_multicast_loop",
                    "native_udp_set_multicast_ttl",
                    "native_udp_set_read_timeout",
                    "native_udp_set_ttl",
                    "native_udp_set_write_timeout",
                ];
                let rt_keep = [
                    "rt_time_now_nanos",
                    "rt_time_now_micros",
                    "rt_time_now_unix_micros",
                    "rt_file_mmap_read_text",
                    "rt_file_mmap_read_bytes",
                    "rt_file_read_text_at",
                    "rt_file_read_bytes_at",
                    "rt_file_write_text_at",
                    "rt_file_write_bytes_at",
                    "rt_mmap",
                    "rt_mmap_raw",
                    "rt_munmap",
                    "rt_munmap_raw",
                    "rt_madvise",
                    "rt_msync",
                    "rt_process_spawn_async",
                    "rt_process_wait",
                    "rt_process_is_running",
                    "rt_process_kill",
                    "rt_hostname",
                    "rt_fault_set_stack_overflow_detection",
                    "rt_fault_set_timeout",
                    "rt_fault_set_execution_limit",
                    "rt_debug_set_active",
                    "rt_debug_enable",
                    "rt_debug_disable",
                    "rt_file_rename",
                    "rt_file_write",
                    "rt_file_delete",
                    "rt_file_size",
                    "rt_file_lock",
                    "rt_getpid",
                    "rt_compile_to_llvm_ir",
                    "rt_file_hash_sha256",
                    "rt_path_parent",
                    "range",
                ];
                for line in String::from_utf8_lossy(&nm_out.stdout).lines() {
                    if let Some(sym) = line.split_whitespace().last() {
                        let keep = sym.starts_with("ds_")
                            || sym.starts_with("get_global_")
                            || sym.starts_with("set_global_")
                            || sym.contains("GLOBAL_LOG_LEVEL")
                            || sym.contains("SCOPE_LEVELS")
                            || extra_keep.contains(&sym)
                            || rt_keep.contains(&sym);
                        if keep {
                            symbols.insert(sym.to_string());
                        }
                    }
                }
            if !symbols.is_empty() {
                // Use a different filename from the first-pass auto-stub so we don't
                // clobber the broad stub set generated from main.o.
                let auto_c = temp_path.join("_bootstrap_auto2.c");
                let auto_o = temp_path.join("_bootstrap_auto2.o");
                let mut code = String::from("#include <stdint.h>\n#include <stdbool.h>\n");
                for sym in &symbols {
                    let is_data = sym.contains("GLOBAL_") || sym.contains("SCOPE_");
                    let valid_ident = sym.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') && sym != "int";
                    if is_data && valid_ident {
                        code.push_str(&format!("__attribute__((weak, used)) int64_t {0} = 0;\n", sym));
                    } else if valid_ident {
                        code.push_str(&format!(
                            "__attribute__((weak, used)) int64_t {0}(void) {{ return 0; }}\n",
                            sym
                        ));
                    } else {
                        let clean = sym.replace('\"', "");
                        code.push_str(&format!(
                            "__asm__(\".weak {0}\\n{0}:\\n  {1}\\n\");\n",
                            clean, ret_insn
                        ));
                    }
                }
                std::fs::write(&auto_c, code)
                    .map_err(|e| LinkerError::LinkFailed(format!("failed to write auto stub: {}", e)))?;
                let cc2 = detect_c_compiler(&self.options.target);
                let status = std::process::Command::new(&cc2)
                    .args(compile_c_args(&cc2, &auto_o, &auto_c))
                    .status()
                    .map_err(|e| LinkerError::LinkFailed(format!("failed to compile auto stub: {}", e)))?;
                if status.success() {
                    bootstrap_stubs.push(auto_o);
                } else {
                    eprintln!(
                        "warning: failed to build auto stub (second pass) with {} (status {})",
                        cc2, status
                    );
                }
            }
            do_link(Path::new(&self.options.output), false, &bootstrap_stubs, require_crypto)
        } else {
            Ok(())
        };

        match final_result {
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
    ///
    /// On Linux/FreeBSD: looks for crt1.o/Scrt1.o, crti.o, crtn.o
    /// On macOS/Windows: returns empty (CRT handled automatically by the toolchain)
    fn find_crt_files(&self) -> LinkerResult<Vec<PathBuf>> {
        use simple_common::target::{TargetArch, TargetOS};
        let mut crt_files = Vec::new();

        match self.options.target.os {
            TargetOS::Linux => {
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
                        crt_files.push(crtn);
                        break;
                    }
                }
            }
            TargetOS::FreeBSD => {
                // FreeBSD uses the same crt scheme, in /usr/lib
                let dir_path = PathBuf::from("/usr/lib");
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
                    crt_files.push(crtn);
                }
            }
            TargetOS::MacOS => {
                // macOS uses -lSystem; no CRT object files needed
                return Ok(crt_files);
            }
            TargetOS::Windows => {
                // MSVC handles CRT automatically; no manual CRT objects needed
                return Ok(crt_files);
            }
            _ => {
                return Ok(crt_files);
            }
        }

        if crt_files.is_empty() && matches!(self.options.target.os, TargetOS::Linux | TargetOS::FreeBSD) {
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
    ///
    /// On Linux: architecture-specific ld-linux paths
    /// On FreeBSD: /libexec/ld-elf.so.1
    /// On macOS/Windows: None (handled automatically by the toolchain)
    fn find_dynamic_linker(&self) -> Option<PathBuf> {
        use simple_common::target::{TargetArch, TargetOS};

        match self.options.target.os {
            TargetOS::Linux => {
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
                if self.options.target.arch != TargetArch::host() {
                    return match self.options.target.arch {
                        TargetArch::X86_64 => Some(PathBuf::from("/lib64/ld-linux-x86-64.so.2")),
                        TargetArch::Aarch64 => Some(PathBuf::from("/lib/ld-linux-aarch64.so.1")),
                        TargetArch::Riscv64 => Some(PathBuf::from("/lib/ld-linux-riscv64-lp64d.so.1")),
                        _ => None,
                    };
                }

                None
            }
            TargetOS::FreeBSD => {
                let p = PathBuf::from("/libexec/ld-elf.so.1");
                if p.exists() || self.options.target.arch != TargetArch::host() {
                    Some(p)
                } else {
                    None
                }
            }
            // macOS: ld64 handles dynamic linking automatically
            // Windows: PE import tables, no Unix-style dynamic linker
            _ => None,
        }
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
            assert!(!paths.is_empty(), "Should detect at least one system library path");
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
        let options = NativeBinaryOptions::new().library("pthread").library("dl").library("m");

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

    // ============================================================================
    // Multiplatform & Multi-CPU Tests
    // ============================================================================

    #[test]
    fn test_default_libraries_linux() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let libs = NativeBinaryOptions::default_libraries_for_target(&target);
        assert!(libs.contains(&"c".to_string()));
        assert!(libs.contains(&"pthread".to_string()));
        assert!(libs.contains(&"dl".to_string()));
        assert!(libs.contains(&"m".to_string()));
        assert!(libs.contains(&"gcc_s".to_string()));
        assert!(libs.contains(&"simple_runtime".to_string()));
    }

    #[test]
    fn test_default_libraries_macos() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        let libs = NativeBinaryOptions::default_libraries_for_target(&target);
        assert!(libs.contains(&"c".to_string()));
        assert!(libs.contains(&"System".to_string()));
        assert!(libs.contains(&"simple_runtime".to_string()));
        // macOS should NOT have pthread/dl/m (provided by -lSystem)
        assert!(!libs.contains(&"pthread".to_string()));
        assert!(!libs.contains(&"dl".to_string()));
    }

    #[test]
    fn test_default_libraries_windows() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Windows);
        let libs = NativeBinaryOptions::default_libraries_for_target(&target);
        assert!(libs.contains(&"c".to_string()));
        assert!(libs.contains(&"msvcrt".to_string()));
        assert!(libs.contains(&"kernel32".to_string()));
        assert!(libs.contains(&"ws2_32".to_string()));
        assert!(libs.contains(&"advapi32".to_string()));
        assert!(libs.contains(&"simple_runtime".to_string()));
    }

    #[test]
    fn test_default_libraries_freebsd() {
        let target = Target::new(TargetArch::X86_64, TargetOS::FreeBSD);
        let libs = NativeBinaryOptions::default_libraries_for_target(&target);
        assert!(libs.contains(&"c".to_string()));
        assert!(libs.contains(&"pthread".to_string()));
        assert!(libs.contains(&"m".to_string()));
        assert!(libs.contains(&"execinfo".to_string()));
        assert!(libs.contains(&"simple_runtime".to_string()));
    }

    #[test]
    fn test_static_lib_name_unix() {
        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(NativeBinaryOptions::static_lib_name("simple_runtime", &linux), "libsimple_runtime.a");

        let macos = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        assert_eq!(NativeBinaryOptions::static_lib_name("simple_runtime", &macos), "libsimple_runtime.a");

        let freebsd = Target::new(TargetArch::X86_64, TargetOS::FreeBSD);
        assert_eq!(NativeBinaryOptions::static_lib_name("simple_compiler", &freebsd), "libsimple_compiler.a");
    }

    #[test]
    fn test_static_lib_name_windows() {
        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);
        assert_eq!(NativeBinaryOptions::static_lib_name("simple_runtime", &windows), "simple_runtime.lib");
        assert_eq!(NativeBinaryOptions::static_lib_name("simple_compiler", &windows), "simple_compiler.lib");
    }

    #[test]
    fn test_asm_ret_instruction_x86_64() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(asm_ret_instruction(&target), "ret");
    }

    #[test]
    fn test_asm_ret_instruction_aarch64() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::Linux);
        assert_eq!(asm_ret_instruction(&target), "ret");
    }

    #[test]
    fn test_asm_ret_instruction_arm32() {
        let target = Target::new(TargetArch::Arm, TargetOS::Linux);
        assert_eq!(asm_ret_instruction(&target), "bx lr");
    }

    #[test]
    fn test_asm_ret_instruction_riscv() {
        let target = Target::new(TargetArch::Riscv64, TargetOS::Linux);
        assert_eq!(asm_ret_instruction(&target), "ret");
    }

    #[test]
    fn test_detect_c_compiler_default() {
        // Without CC env var set, should return platform-appropriate default
        let saved = std::env::var("CC").ok();
        std::env::remove_var("CC");

        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(detect_c_compiler(&linux), "cc");

        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);
        assert_eq!(detect_c_compiler(&windows), "cl.exe");

        // Restore CC if it was set
        if let Some(cc) = saved {
            std::env::set_var("CC", cc);
        }
    }

    #[test]
    fn test_is_msvc_compiler() {
        assert!(is_msvc_compiler("cl"));
        assert!(is_msvc_compiler("cl.exe"));
        assert!(is_msvc_compiler("CL.EXE"));
        assert!(!is_msvc_compiler("gcc"));
        assert!(!is_msvc_compiler("cc"));
        assert!(!is_msvc_compiler("clang"));
    }

    #[test]
    fn test_compile_c_args_gnu() {
        let args = compile_c_args("cc", Path::new("out.o"), Path::new("in.c"));
        assert_eq!(args, vec!["-c", "-o", "out.o", "in.c"]);
    }

    #[test]
    fn test_compile_c_args_msvc() {
        let args = compile_c_args("cl.exe", Path::new("out.obj"), Path::new("in.c"));
        assert_eq!(args, vec!["/c", "/Foout.obj", "in.c"]);
    }

    #[test]
    fn test_detect_nm_command_unix() {
        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let (cmd, args) = detect_nm_command(&linux);
        assert_eq!(cmd, "nm");
        assert_eq!(args, vec!["-u"]);
    }

    #[test]
    fn test_library_paths_for_linux_x86_64() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        // On a Linux x86_64 system, should find some paths
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        assert!(!paths.is_empty());
        // On other systems, just ensure it doesn't panic
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_windows() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Windows);
        // Should not panic even without Windows SDK installed
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_freebsd() {
        let target = Target::new(TargetArch::X86_64, TargetOS::FreeBSD);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        // On FreeBSD, should find /usr/lib; on other systems just don't panic
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_macos() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        let _ = paths;
    }
}
