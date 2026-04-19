//! Options and library-path detection for native binary builds.

use std::path::{Path, PathBuf};

use simple_common::target::{LinkerFlavor, Target, TargetArch, TargetOS};

use super::native::NativeLinker;

/// Get the architecture-appropriate `ret` instruction for inline asm stubs.
/// Delegates to `simple_common::platform::asm_helpers`.
pub(super) fn asm_ret_instruction(target: &Target) -> &'static str {
    simple_common::platform::asm_helpers::asm_ret_instruction(target)
}

/// Detect the C compiler for the target platform.
/// Delegates to `simple_common::platform::cc_detect`.
pub(super) fn detect_c_compiler(target: &Target) -> String {
    simple_common::platform::cc_detect::detect_c_compiler_for_target(target)
}

/// Build arguments for compiling a C file to an object file.
///
/// Returns (args_before_output, output_flag, args_after_output) based on compiler type.
/// MSVC uses `/c /Fo<out>`, GNU uses `-c -o <out>`.
pub(super) fn compile_c_args(cc: &str, output: &Path, input: &Path) -> Vec<String> {
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
pub(super) fn is_msvc_compiler(cc: &str) -> bool {
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
pub(super) fn detect_nm_command(target: &Target) -> (String, Vec<String>) {
    if target.os == TargetOS::Windows {
        // Try dumpbin first (MSVC tool)
        if std::process::Command::new("dumpbin")
            .arg("/?")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return ("dumpbin".to_string(), vec!["/SYMBOLS".to_string()]);
        }
        // Try llvm-nm
        if std::process::Command::new("llvm-nm")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
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
    /// Delegates to `simple_common::platform::link_config`.
    pub fn default_libraries_for_target(target: &Target) -> Vec<String> {
        simple_common::platform::link_config::default_libraries_for_target(target)
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
                // On modern macOS, system libraries are TBD stubs inside the SDK.
                // Detect SDK path via xcrun for reliable library resolution.
                if let Ok(output) = std::process::Command::new("xcrun").args(["--show-sdk-path"]).output() {
                    if output.status.success() {
                        let sdk = String::from_utf8_lossy(&output.stdout).trim().to_string();
                        let sdk_lib = PathBuf::from(&sdk).join("usr/lib");
                        if sdk_lib.exists() {
                            paths.push(sdk_lib);
                        }
                    }
                }
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
                                let p = PathBuf::from(&sdk_dir)
                                    .join("Lib")
                                    .join(version)
                                    .join(subdir)
                                    .join(arch_subdir);
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
    /// Returns `lib{base}.a` on Unix and MinGW, `{base}.lib` on MSVC Windows.
    pub fn static_lib_name(base: &str, target: &Target) -> String {
        match target.linker_flavor() {
            LinkerFlavor::Msvc => format!("{}.lib", base),
            _ => format!("lib{}.a", base),
        }
    }

    /// Check if a directory contains the Simple runtime library.
    ///
    /// On Windows, checks for both `libsimple_runtime.a` (MinGW) and
    /// `simple_runtime.lib` (MSVC) since either toolchain may be in use.
    fn runtime_lib_exists(dir: &Path) -> bool {
        dir.join("libsimple_runtime.a").exists() || dir.join("simple_runtime.lib").exists()
    }

    /// Find the Simple runtime library path.
    ///
    /// Looks for libsimple_runtime.a (or simple_runtime.lib on Windows) in:
    /// 1. SIMPLE_RUNTIME_PATH environment variable
    /// 2. Adjacent to the current executable (for installed binaries)
    /// 3. Cargo target directory (for development)
    pub fn find_runtime_library_path() -> Option<PathBuf> {
        // Check environment variable first (runtime)
        if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
            let p = PathBuf::from(&path);
            if p.exists() {
                return Some(p);
            }
        }

        // Check compile-time embedded path (for bootstrapped binaries)
        if let Some(path) = option_env!("SIMPLE_RUNTIME_PATH") {
            let p = PathBuf::from(path);
            if p.exists() {
                return Some(p);
            }
        }

        // Check adjacent to current executable (e.g., /usr/lib/simple/)
        if let Ok(exe_path) = std::env::current_exe() {
            if let Some(exe_dir) = exe_path.parent() {
                // Check ../lib relative to executable
                let lib_dir = exe_dir.join("../lib");
                if Self::runtime_lib_exists(&lib_dir) {
                    return lib_dir.canonicalize().ok();
                }

                // Check same directory as executable
                if Self::runtime_lib_exists(exe_dir) {
                    return Some(exe_dir.to_path_buf());
                }

                // Check deps/ subdirectory (for bootstrap/custom profiles)
                let deps_dir = exe_dir.join("deps");
                if Self::runtime_lib_exists(&deps_dir) {
                    return deps_dir.canonicalize().ok();
                }
            }
        }

        // Check cargo target directory (for development)
        // Try release, debug, and bootstrap directories (including deps/ for profile builds)
        let cargo_target_paths = [
            // Standard cargo target directory
            "target/release",
            "target/debug",
            "target/bootstrap",
            "target/bootstrap/deps",
            // Rust compiler subdirectory (Simple project layout)
            "src/compiler_rust/target/release",
            "src/compiler_rust/target/debug",
            "src/compiler_rust/target/bootstrap",
            "src/compiler_rust/target/bootstrap/deps",
            // Workspace root (when running from subdirectory)
            "../target/release",
            "../target/debug",
            "../target/bootstrap",
            "../target/bootstrap/deps",
            "../../target/release",
            "../../target/debug",
            "../../target/bootstrap",
            "../../target/bootstrap/deps",
        ];

        for path in cargo_target_paths {
            let p = PathBuf::from(path);
            if Self::runtime_lib_exists(&p) {
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
                for profile in ["release", "debug", "bootstrap"] {
                    let lib_path = root.join("target").join(profile);
                    if Self::runtime_lib_exists(&lib_path) {
                        return Some(lib_path);
                    }
                    // Also check deps/ subdirectory (custom profiles put libs there)
                    let deps_path = lib_path.join("deps");
                    if Self::runtime_lib_exists(&deps_path) {
                        return Some(deps_path);
                    }
                }
            }
        }

        None
    }

    /// Check if a directory contains the Simple compiler library.
    fn compiler_lib_exists(dir: &Path) -> bool {
        dir.join("libsimple_compiler.a").exists() || dir.join("simple_compiler.lib").exists()
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
                if Self::compiler_lib_exists(&lib_dir) {
                    return lib_dir.canonicalize().ok();
                }
                if Self::compiler_lib_exists(exe_dir) {
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
            if Self::compiler_lib_exists(&p) {
                return p.canonicalize().ok();
            }
        }

        // Check workspace root from manifest dir
        if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
            let workspace_root = PathBuf::from(&manifest_dir).ancestors().nth(1).map(|p| p.to_path_buf());

            if let Some(root) = workspace_root {
                for profile in ["release", "debug"] {
                    let lib_path = root.join("target").join(profile);
                    if Self::compiler_lib_exists(&lib_path) {
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
