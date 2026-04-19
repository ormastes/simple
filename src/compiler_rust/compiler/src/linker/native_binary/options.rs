use std::path::{Path, PathBuf};
use std::process::Command;

use simple_common::target::{LinkerFlavor, Target, TargetArch, TargetOS};

use crate::linker::native::NativeLinker;

pub(super) fn asm_ret_instruction(target: &Target) -> &'static str {
    simple_common::platform::asm_helpers::asm_ret_instruction(target)
}

pub(super) fn detect_c_compiler(target: &Target) -> String {
    simple_common::platform::cc_detect::detect_c_compiler_for_target(target)
}

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

pub(super) fn is_msvc_compiler(cc: &str) -> bool {
    let base = std::path::Path::new(cc)
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(cc);
    base.eq_ignore_ascii_case("cl") || base.eq_ignore_ascii_case("cl.exe")
}

pub(super) fn detect_nm_command(target: &Target) -> (String, Vec<String>) {
    if target.os == TargetOS::Windows {
        if Command::new("dumpbin")
            .arg("/?")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return ("dumpbin".to_string(), vec!["/SYMBOLS".to_string()]);
        }
        if Command::new("llvm-nm")
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
    pub output: PathBuf,
    pub target: Target,
    pub layout_optimize: bool,
    pub layout_profile: Option<PathBuf>,
    pub strip: bool,
    pub pie: bool,
    pub shared: bool,
    pub libraries: Vec<String>,
    pub library_paths: Vec<PathBuf>,
    pub linker: Option<NativeLinker>,
    pub generate_map: bool,
    pub verbose: bool,
}

impl Default for NativeBinaryOptions {
    fn default() -> Self {
        let mut library_paths = Self::detect_system_library_paths();

        if let Some(runtime_path) = Self::find_runtime_library_path() {
            library_paths.insert(0, runtime_path);
        } else {
            let cwd_debug = std::env::current_dir().ok().map(|p| p.join("target/debug"));
            if let Some(path) = cwd_debug {
                if path.join("libsimple_runtime.a").exists() {
                    library_paths.insert(0, path);
                }
            }
        }

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
            pie: true,
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
    pub(super) fn detect_system_library_paths() -> Vec<PathBuf> {
        Self::detect_library_paths_for_target(&Target::host())
    }

    pub fn default_libraries_for_target(target: &Target) -> Vec<String> {
        simple_common::platform::link_config::default_libraries_for_target(target)
    }

    pub fn detect_library_paths_for_target(target: &Target) -> Vec<PathBuf> {
        let mut paths = Vec::new();

        match target.os {
            TargetOS::Linux => {
                let arch_dirs: &[&str] = match target.arch {
                    TargetArch::X86_64 => &[
                        "/lib/x86_64-linux-gnu",
                        "/usr/lib/x86_64-linux-gnu",
                        "/lib64",
                        "/usr/lib64",
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

                for path in ["/lib", "/usr/lib"] {
                    let p = PathBuf::from(path);
                    if p.exists() {
                        paths.push(p);
                    }
                }
            }
            TargetOS::MacOS => {
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
                let arch_subdir = match target.arch {
                    TargetArch::X86_64 => "x64",
                    TargetArch::Aarch64 => "arm64",
                    TargetArch::X86 => "x86",
                    TargetArch::Arm => "arm",
                    _ => "x64",
                };

                for env_var in ["UniversalCRTSdkDir", "WindowsSdkDir"] {
                    if let Ok(sdk_dir) = std::env::var(env_var) {
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

    pub fn static_lib_name(base: &str, target: &Target) -> String {
        match target.linker_flavor() {
            LinkerFlavor::Msvc => format!("{}.lib", base),
            _ => format!("lib{}.a", base),
        }
    }

    fn runtime_lib_exists(dir: &Path) -> bool {
        dir.join("libsimple_runtime.a").exists() || dir.join("simple_runtime.lib").exists()
    }

    pub fn find_runtime_library_path() -> Option<PathBuf> {
        if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
            let p = PathBuf::from(&path);
            if p.exists() {
                return Some(p);
            }
        }

        if let Some(path) = option_env!("SIMPLE_RUNTIME_PATH") {
            let p = PathBuf::from(path);
            if p.exists() {
                return Some(p);
            }
        }

        if let Ok(exe_path) = std::env::current_exe() {
            if let Some(exe_dir) = exe_path.parent() {
                let lib_dir = exe_dir.join("../lib");
                if Self::runtime_lib_exists(&lib_dir) {
                    return lib_dir.canonicalize().ok();
                }

                if Self::runtime_lib_exists(exe_dir) {
                    return Some(exe_dir.to_path_buf());
                }

                let deps_dir = exe_dir.join("deps");
                if Self::runtime_lib_exists(&deps_dir) {
                    return deps_dir.canonicalize().ok();
                }
            }
        }

        let cargo_target_paths = [
            "target/release",
            "target/debug",
            "target/bootstrap",
            "target/bootstrap/deps",
            "src/compiler_rust/target/release",
            "src/compiler_rust/target/debug",
            "src/compiler_rust/target/bootstrap",
            "src/compiler_rust/target/bootstrap/deps",
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

        if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
            let workspace_root = PathBuf::from(&manifest_dir)
                .ancestors()
                .nth(1)
                .map(|p| p.to_path_buf());

            if let Some(root) = workspace_root {
                for profile in ["release", "debug", "bootstrap"] {
                    let lib_path = root.join("target").join(profile);
                    if Self::runtime_lib_exists(&lib_path) {
                        return Some(lib_path);
                    }
                    let deps_path = lib_path.join("deps");
                    if Self::runtime_lib_exists(&deps_path) {
                        return Some(deps_path);
                    }
                }
            }
        }

        None
    }

    fn compiler_lib_exists(dir: &Path) -> bool {
        dir.join("libsimple_compiler.a").exists() || dir.join("simple_compiler.lib").exists()
    }

    pub fn find_compiler_library_path() -> Option<PathBuf> {
        if let Ok(path) = std::env::var("SIMPLE_COMPILER_PATH") {
            let p = PathBuf::from(&path);
            if p.exists() {
                return Some(p);
            }
        }

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

    pub fn new() -> Self {
        Self::default()
    }

    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.output = path.into();
        self
    }

    impl_target_method!(direct);
    impl_layout_methods!(direct);
    impl_bool_flag_methods!(direct);
    impl_linker_builder_methods!(direct);
    impl_linker_method!(direct);
}
