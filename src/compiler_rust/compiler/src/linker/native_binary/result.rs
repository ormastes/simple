use std::path::PathBuf;

use crate::linker::error::{LinkerError, LinkerResult};
use crate::linker::layout::LayoutOptimizer;

use super::builder::NativeBinaryBuilder;
use super::options::{NativeBinaryOptions, asm_ret_instruction, detect_c_compiler};

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
/// Convenience function combining compilation and linking.
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

    let mut parser = simple_parser::Parser::new(source);
    let ast_module = parser
        .parse()
        .map_err(|e| LinkerError::LinkFailed(format!("parse error: {}", e)))?;

    let hir_module =
        hir::lower(&ast_module).map_err(|e| LinkerError::LinkFailed(format!("HIR lowering error: {}", e)))?;

    let mir_module =
        mir::lower_to_mir(&hir_module).map_err(|e| LinkerError::LinkFailed(format!("MIR lowering error: {}", e)))?;

    let codegen =
        Codegen::for_target(options.target).map_err(|e| LinkerError::LinkFailed(format!("codegen error: {}", e)))?;
    let object_code = codegen
        .compile_module(&mir_module)
        .map_err(|e| LinkerError::LinkFailed(format!("compilation error: {}", e)))?;

    let mut builder = NativeBinaryBuilder::new(object_code).options(options);

    if builder.options.layout_optimize {
        let optimizer = LayoutOptimizer::new();
        builder = builder.with_layout_optimizer(optimizer);
    }

    builder.build()
}

#[cfg(test)]
mod tests {
    use simple_common::target::{Target, TargetArch, TargetOS};

    use super::*;
    use crate::linker::layout::LayoutOptimizer;
    use crate::linker::native_binary::builder::NativeBinaryBuilder;
    use crate::linker::native_binary::options::{
        asm_ret_instruction, compile_c_args, detect_c_compiler, detect_nm_command, is_msvc_compiler,
        NativeBinaryOptions,
    };

    use std::path::Path;

    #[test]
    fn test_options_default() {
        let options = NativeBinaryOptions::default();
        assert!(options.pie);
        assert!(!options.strip);
        assert!(!options.shared);
        #[cfg(target_os = "macos")]
        assert!(options.libraries.contains(&"System".to_string()));
        #[cfg(not(target_os = "macos"))]
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

        assert_eq!(options.output, std::path::PathBuf::from("test"));
        assert!(options.strip);
        assert!(!options.pie);
        assert!(options.libraries.contains(&"m".to_string()));
        assert!(options.verbose);
    }

    #[test]
    fn test_builder_creation() {
        let builder = NativeBinaryBuilder::new(vec![1, 2, 3, 4]).output("test").strip(true);

        assert_eq!(builder.options.output, std::path::PathBuf::from("test"));
        assert!(builder.options.strip);
    }

    #[test]
    fn test_library_path_detection() {
        let paths = NativeBinaryOptions::detect_system_library_paths();
        #[cfg(target_family = "unix")]
        {
            assert!(!paths.is_empty(), "Should detect at least one system library path");
        }
    }

    #[test]
    fn test_find_runtime_library() {
        let runtime_path = NativeBinaryOptions::find_runtime_library_path();
        if let Some(path) = runtime_path {
            assert!(
                path.is_dir() || path.parent().map(|p| p.is_dir()).unwrap_or(false),
                "Runtime path should be a directory: {:?}",
                path
            );
        }
    }

    #[test]
    fn test_options_with_multiple_libraries() {
        let options = NativeBinaryOptions::new().library("pthread").library("dl").library("m");
        assert!(options.libraries.contains(&"pthread".to_string()));
        assert!(options.libraries.contains(&"dl".to_string()));
        assert!(options.libraries.contains(&"m".to_string()));
    }

    #[test]
    fn test_options_with_library_paths() {
        let path1 = std::path::PathBuf::from("/usr/lib");
        let path2 = std::path::PathBuf::from("/usr/local/lib");

        let options = NativeBinaryOptions::new()
            .library_path(path1.clone())
            .library_path(path2.clone());

        assert!(options.library_paths.contains(&path1));
        assert!(options.library_paths.contains(&path2));
    }

    #[test]
    fn test_shared_library_mode() {
        let options = NativeBinaryOptions::new().shared(true).pie(false);
        assert!(options.shared);
        assert!(!options.pie);
    }

    #[test]
    fn test_layout_optimization_enabled() {
        let options = NativeBinaryOptions::new().layout_optimize(true);
        assert!(options.layout_optimize);
    }

    #[test]
    fn test_layout_profile_path() {
        let profile_path = std::path::PathBuf::from("/tmp/profile.data");
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

        assert_eq!(builder.options.output, std::path::PathBuf::from("myapp"));
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
        let code = vec![0x7f, 0x45, 0x4c, 0x46];
        let builder = NativeBinaryBuilder::new(code.clone());
        assert_eq!(builder.object_code, code);
    }

    #[test]
    fn test_output_path_relative() {
        let options = NativeBinaryOptions::new().output("bin/myapp");
        assert_eq!(options.output, std::path::PathBuf::from("bin/myapp"));
    }

    #[test]
    fn test_output_path_absolute() {
        let options = NativeBinaryOptions::new().output("/usr/local/bin/myapp");
        assert_eq!(options.output, std::path::PathBuf::from("/usr/local/bin/myapp"));
    }

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
        assert!(libs.contains(&"System".to_string()));
        assert!(libs.contains(&"simple_runtime".to_string()));
        assert!(!libs.contains(&"c".to_string()));
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
        assert_eq!(
            NativeBinaryOptions::static_lib_name("simple_runtime", &linux),
            "libsimple_runtime.a"
        );

        let macos = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        assert_eq!(
            NativeBinaryOptions::static_lib_name("simple_runtime", &macos),
            "libsimple_runtime.a"
        );

        let freebsd = Target::new(TargetArch::X86_64, TargetOS::FreeBSD);
        assert_eq!(
            NativeBinaryOptions::static_lib_name("simple_compiler", &freebsd),
            "libsimple_compiler.a"
        );
    }

    #[test]
    fn test_static_lib_name_windows() {
        let saved = std::env::var("SIMPLE_LINKER_FLAVOR").ok();
        std::env::set_var("SIMPLE_LINKER_FLAVOR", "msvc");

        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);
        assert_eq!(
            NativeBinaryOptions::static_lib_name("simple_runtime", &windows),
            "simple_runtime.lib"
        );
        assert_eq!(
            NativeBinaryOptions::static_lib_name("simple_compiler", &windows),
            "simple_compiler.lib"
        );

        match saved {
            Some(v) => std::env::set_var("SIMPLE_LINKER_FLAVOR", v),
            None => std::env::remove_var("SIMPLE_LINKER_FLAVOR"),
        }
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
        let saved = std::env::var("CC").ok();
        std::env::remove_var("CC");

        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(detect_c_compiler(&linux), "cc");

        let windows = Target::new(TargetArch::X86_64, TargetOS::Windows);
        let win_cc = detect_c_compiler(&windows);
        assert!(
            win_cc == "cl.exe" || win_cc == "gcc" || win_cc == "cc",
            "unexpected Windows C compiler: {win_cc}"
        );

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
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        assert!(!paths.is_empty());
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_windows() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Windows);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_freebsd() {
        let target = Target::new(TargetArch::X86_64, TargetOS::FreeBSD);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        let _ = paths;
    }

    #[test]
    fn test_library_paths_for_macos() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::MacOS);
        let paths = NativeBinaryOptions::detect_library_paths_for_target(&target);
        let _ = paths;
    }
}
