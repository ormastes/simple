//! Compilation command handlers

use std::path::PathBuf;
use simple_common::target::{NativeCodegenBackend, Target, TargetCpu};
use simple_compiler::linker::NativeLinker;
use simple_compiler::ProjectContext;
use simple_compiler::optimizations::{format_optimization_guide, NativeOptimizationLevel};
use simple_compiler::{default_native_codegen_backend, is_native_codegen_backend_available};
use crate::cli::compile::{
    compile_dynamic_driver_library, compile_file, compile_file_native, compile_file_to_ptx, compile_file_to_vhdl,
    list_linkers, list_targets,
    NativeStripMode,
};
use crate::CompileOptions;

/// Handle 'compile' command - compile source to SMF or native binary
pub fn handle_compile(args: &[String]) -> i32 {
    if args.iter().any(|a| a == "--list-optimizations") {
        println!("{}", format_optimization_guide());
        return 0;
    }
    if args.iter().any(|a| a == "--list-targets") {
        return list_targets();
    }
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_compile_help(false);
        return 0;
    }

    let Some(source) = parse_source_arg(args) else {
        print_compile_help(true);
        return 1;
    };

    let output = args
        .iter()
        .position(|a| a == "-o")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);

    // Parse flags
    let native = args.iter().any(|a| a == "--native");
    let snapshot = args.iter().any(|a| a == "--snapshot");
    let driver_mode = match parse_driver_mode_flag(args) {
        Ok(mode) => mode,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // Parse backend
    let backend = match parse_backend_flag(args) {
        Ok(backend) => backend,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // CUDA/PTX backend - generate PTX output
    if let Some(ref b) = backend {
        if b == "cuda" || b == "ptx" {
            return compile_file_to_ptx(&source, output);
        }
        if b == "vhdl" {
            return compile_file_to_vhdl(&source, output);
        }
    }

    // Parse target architecture
    let target = match parse_target_flag(args) {
        Ok(target) => target,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    let cpu = match parse_cpu_flag(args) {
        Ok(cpu) => cpu,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // Parse linker
    let linker = match parse_linker_flag(args) {
        Ok(linker) => linker,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // Print linker info if specified
    if let Some(l) = linker {
        if !NativeLinker::is_available(l) {
            eprintln!("warning: linker '{}' not found on system", l.name());
        } else if native {
            println!("Using linker: {}", l.name());
        }
    }

    if let Some(mode) = driver_mode {
        if mode != "dynamic" {
            eprintln!("error: unknown driver mode '{}'; supported: dynamic", mode);
            return 1;
        }
        let options = CompileOptions::from_args(args);
        compile_dynamic_driver_library(&source, output, target, snapshot, options)
    } else if native {
        let opt_level = match parse_opt_level_flag(args) {
            Ok(level) => level.unwrap_or_else(NativeOptimizationLevel::default_for_native_executable),
            Err(err) => {
                eprintln!("error: {}", err);
                return 1;
            }
        };

        // Parse native binary options
        let layout_optimize = args.iter().any(|a| a == "--layout-optimize") || opt_level.enables_layout_optimize();
        let pie = !args.iter().any(|a| a == "--no-pie");
        let shared = args.iter().any(|a| a == "--shared");
        let generate_map = args.iter().any(|a| a == "--map");

        let resolved = match resolve_native_build_policy(&source, target, cpu, backend.as_deref()) {
            Ok(policy) => policy,
            Err(err) => {
                eprintln!("error: {}", err);
                return 1;
            }
        };
        let strip_mode = resolve_native_strip_mode(args, resolved.target, shared);

        compile_file_native(
            &source,
            output,
            Some(resolved.target),
            Some(resolved.backend),
            Some(resolved.cpu),
            linker,
            opt_level,
            layout_optimize,
            strip_mode,
            pie,
            shared,
            generate_map,
        )
    } else {
        // Compile to SMF
        let options = CompileOptions::from_args(args);
        compile_file(&source, output, target, snapshot, options)
    }
}

/// Handle 'targets' command - list available compilation targets
pub fn handle_targets() -> i32 {
    list_targets()
}

/// Handle 'linkers' command - list available native linkers
pub fn handle_linkers() -> i32 {
    list_linkers()
}

fn parse_target_flag(args: &[String]) -> Result<Option<Target>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--target" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--target requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--target=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|value| Target::parse(&value).map_err(|e| e.to_string()))
        .transpose()
}

fn parse_linker_flag(args: &[String]) -> Result<Option<NativeLinker>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--linker" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--linker requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--linker=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|s| NativeLinker::from_name(&s).ok_or_else(|| format!("unknown linker '{}'. Available: mold, lld, ld", s)))
        .transpose()
}

fn parse_backend_flag(args: &[String]) -> Result<Option<String>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--backend" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--backend requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--backend=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()
}

fn parse_cpu_flag(args: &[String]) -> Result<Option<TargetCpu>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--cpu" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--cpu requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--cpu=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|value| value.parse::<TargetCpu>().map_err(|e| e.to_string()))
        .transpose()
}

fn parse_opt_level_flag(args: &[String]) -> Result<Option<NativeOptimizationLevel>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--opt-level" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--opt-level requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--opt-level=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|value| NativeOptimizationLevel::parse(&value))
        .transpose()
}

fn parse_source_arg(args: &[String]) -> Option<PathBuf> {
    let mut skip_next = false;
    args.iter().skip(1).find_map(|arg| {
        if skip_next {
            skip_next = false;
            return None;
        }
        if matches!(
            arg.as_str(),
            "-o" | "--output" | "--target" | "--linker" | "--driver-mode" | "--opt-level" | "--backend" | "--cpu"
        ) {
            skip_next = true;
            return None;
        }
        if arg.starts_with('-') {
            return None;
        }
        Some(PathBuf::from(arg))
    })
}

fn resolve_native_strip_mode(args: &[String], target: Target, shared: bool) -> NativeStripMode {
    if args.iter().any(|a| a == "--no-strip") {
        return NativeStripMode::None;
    }
    if args.iter().any(|a| a == "--strip") {
        return NativeStripMode::All;
    }
    if target == Target::host() && !shared {
        NativeStripMode::Debug
    } else {
        NativeStripMode::None
    }
}

#[derive(Debug, Clone)]
struct NativeBuildPolicy {
    target: Target,
    cpu: TargetCpu,
    backend: NativeCodegenBackend,
}

#[derive(Debug, Default, Clone)]
struct NativePolicyConfig {
    target: Option<String>,
    cpu: Option<String>,
    backend: Option<String>,
}

fn resolve_native_build_policy(
    source: &std::path::Path,
    cli_target: Option<Target>,
    cli_cpu: Option<TargetCpu>,
    cli_backend: Option<&str>,
) -> Result<NativeBuildPolicy, String> {
    let project = load_project_native_policy(source)?;
    let user = load_user_native_policy()?;

    let target = if let Some(target) = cli_target {
        target
    } else if let Some(value) = project.target.as_deref().or(user.target.as_deref()) {
        Target::parse(value).map_err(|e| format!("invalid configured target '{}': {}", value, e))?
    } else {
        Target::host()
    };

    let cpu = if let Some(cpu) = cli_cpu {
        cpu
    } else if let Some(value) = project.cpu.as_deref().or(user.cpu.as_deref()) {
        value
            .parse::<TargetCpu>()
            .map_err(|e| format!("invalid configured cpu '{}': {}", value, e))?
    } else {
        TargetCpu::builtin_default_for_arch(target.arch)
    };

    let backend = if let Some(value) = cli_backend {
        parse_native_backend_name(value)?
    } else if let Some(value) = project.backend.as_deref().or(user.backend.as_deref()) {
        parse_native_backend_name(value)?
    } else {
        default_native_codegen_backend()
    };

    if !is_native_codegen_backend_available(backend) {
        return Err(format!(
            "native backend '{}' is not available in this build; rebuild with --features llvm or use --backend cranelift",
            backend
        ));
    }

    Ok(NativeBuildPolicy { target, cpu, backend })
}

fn parse_native_backend_name(value: &str) -> Result<NativeCodegenBackend, String> {
    match value.parse::<NativeCodegenBackend>() {
        Ok(backend) => Ok(backend),
        Err(_) => Err(format!("unsupported native backend '{}'; use llvm or cranelift", value)),
    }
}

fn load_project_native_policy(source: &std::path::Path) -> Result<NativePolicyConfig, String> {
    let project = ProjectContext::detect(source).map_err(|e| format!("failed to detect project config: {}", e))?;
    let manifest = project.root.join("simple.toml");
    if manifest.exists() {
        load_native_policy_from_file(&manifest)
    } else {
        Ok(NativePolicyConfig::default())
    }
}

fn load_user_native_policy() -> Result<NativePolicyConfig, String> {
    let Some(home) = dirs_next::home_dir() else {
        return Ok(NativePolicyConfig::default());
    };
    let config = home.join(".simple").join("config.toml");
    if config.exists() {
        load_native_policy_from_file(&config)
    } else {
        Ok(NativePolicyConfig::default())
    }
}

fn load_native_policy_from_file(path: &std::path::Path) -> Result<NativePolicyConfig, String> {
    let content = std::fs::read_to_string(path).map_err(|e| format!("failed to read {}: {}", path.display(), e))?;
    let value: toml::Value = content
        .parse()
        .map_err(|e| format!("failed to parse {}: {}", path.display(), e))?;
    Ok(extract_native_policy(&value))
}

fn extract_native_policy(value: &toml::Value) -> NativePolicyConfig {
    if let Some(table) = [
        value.get("compile").and_then(|v| v.as_table()),
        value.get("native").and_then(|v| v.as_table()),
        value
            .get("build")
            .and_then(|v| v.get("native"))
            .and_then(|v| v.as_table()),
        value
            .get("compile")
            .and_then(|v| v.get("native"))
            .and_then(|v| v.as_table()),
    ]
    .into_iter()
    .flatten()
    .next()
    {
        return NativePolicyConfig {
            target: table.get("target").and_then(|v| v.as_str()).map(ToString::to_string),
            cpu: table.get("cpu").and_then(|v| v.as_str()).map(ToString::to_string),
            backend: table.get("backend").and_then(|v| v.as_str()).map(ToString::to_string),
        };
    }

    NativePolicyConfig::default()
}

fn parse_driver_mode_flag(args: &[String]) -> Result<Option<String>, String> {
    for (idx, arg) in args.iter().enumerate() {
        if arg == "--driver-mode" {
            return args
                .get(idx + 1)
                .cloned()
                .map(Some)
                .ok_or_else(|| "--driver-mode requires a value".to_string());
        }
        if let Some(value) = arg.strip_prefix("--driver-mode=") {
            return Ok(Some(value.to_string()));
        }
    }
    Ok(None)
}

fn print_compile_help(show_error: bool) {
    if show_error {
        eprintln!("error: compile requires a source file");
    }
    eprintln!(
        "Usage: simple compile <source.spl> [-o <output>] [--native] [--driver-mode=dynamic] [--backend=<name>] [--target <target>] [--cpu <policy>] [--linker <name>] [--opt-level <level>] [--snapshot]"
    );
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -o <output>         Output file (default: source.smf or source for --native)");
    eprintln!("  --native            Compile to standalone native binary (ELF/PE)");
    eprintln!("  --list-optimizations  Print implemented optimization groups and levels");
    eprintln!("  --driver-mode=dynamic  Package the compiled driver SMF as a loadable .lsm archive");
    eprintln!("  --backend=<name>    Native backend: llvm|cranelift; or cuda/ptx, vhdl for source emitters");
    eprintln!("  --target <target>   Target triple or arch (x86_64, aarch64, wasm32-wasi, etc.)");
    eprintln!("  --target=<target>   Same as above");
    eprintln!("  --cpu <policy>      Native CPU policy: default, native, x86-64-v1..v4, or backend CPU string");
    eprintln!("  --cpu=<policy>      Same as above");
    eprintln!("  --linker <name>     Native linker to use (mold, lld, ld)");
    eprintln!("  --linker=<name>     Same as above");
    eprintln!("  --opt-level <level> Native optimization level: none, basic, standard, aggressive");
    eprintln!("                     Default for --native: aggressive");
    eprintln!("  --layout-optimize   Force-enable 4KB page layout optimization");
    eprintln!("  --strip             Strip all symbols from output");
    eprintln!("  --no-strip          Keep debug info and symbols (default only overrides host --native auto-strip)");
    eprintln!("  --pie               Create position-independent executable (default)");
    eprintln!("  --no-pie            Disable position-independent executable");
    eprintln!("  --shared            Create shared library (.so/.dll)");
    eprintln!("  --map               Generate linker map file");
    eprintln!("  --snapshot          Create JJ snapshot with build state");
    eprintln!("  --coverage          Enable coverage instrumentation (#674)");
    eprintln!("  --coverage-output=<path>  Output path for coverage report (default: coverage.sdn)");
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    struct EnvVarGuard {
        key: &'static str,
        previous: Option<String>,
    }

    impl EnvVarGuard {
        fn set(key: &'static str, value: &std::path::Path) -> Self {
            let previous = std::env::var(key).ok();
            std::env::set_var(key, value);
            Self { key, previous }
        }
    }

    impl Drop for EnvVarGuard {
        fn drop(&mut self) {
            if let Some(value) = &self.previous {
                std::env::set_var(self.key, value);
            } else {
                std::env::remove_var(self.key);
            }
        }
    }

    fn write_project_manifest(dir: &TempDir, body: &str) -> std::path::PathBuf {
        let src = dir.path().join("src");
        fs::create_dir_all(&src).unwrap();
        let manifest = format!(
            r#"[project]
name = "test-project"

{}"#,
            body
        );
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();
        let source = src.join("main.spl");
        fs::write(&source, "fn main() -> i32:\n    return 0\n").unwrap();
        source
    }

    #[test]
    fn test_parse_target_flag() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--target".to_string(),
            "x86_64".to_string(),
        ];
        let target = parse_target_flag(&args).unwrap();
        assert!(target.is_some());
    }

    #[test]
    fn test_parse_cpu_flag() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--cpu=x86-64-v4".to_string(),
        ];
        let cpu = parse_cpu_flag(&args).unwrap().unwrap();
        assert_eq!(cpu, TargetCpu::X86_64V4);
    }

    #[test]
    fn test_extract_native_policy_prefers_compile_table() {
        let value: toml::Value = r#"
[compile]
target = "aarch64"
cpu = "native"
backend = "llvm"
"#
        .parse()
        .unwrap();

        let policy = extract_native_policy(&value);
        assert_eq!(policy.target.as_deref(), Some("aarch64"));
        assert_eq!(policy.cpu.as_deref(), Some("native"));
        assert_eq!(policy.backend.as_deref(), Some("llvm"));
    }

    #[test]
    fn test_resolve_native_build_policy_prefers_cli_over_project_and_user() {
        let project = tempfile::tempdir().unwrap();
        let source = write_project_manifest(
            &project,
            r#"
[compile]
target = "riscv64"
cpu = "x86-64-v2"
backend = "cranelift"
"#,
        );

        let user_home = tempfile::tempdir().unwrap();
        let simple_dir = user_home.path().join(".simple");
        fs::create_dir_all(&simple_dir).unwrap();
        fs::write(
            simple_dir.join("config.toml"),
            r#"
[compile]
target = "aarch64"
cpu = "native"
backend = "llvm"
"#,
        )
        .unwrap();
        let _home = EnvVarGuard::set("HOME", user_home.path());
        let cli_backend = default_native_codegen_backend();
        let cli_backend_name = if cli_backend == NativeCodegenBackend::Llvm {
            "llvm"
        } else {
            "cranelift"
        };

        let policy = resolve_native_build_policy(
            &source,
            Some(Target::parse("x86_64").unwrap()),
            Some(TargetCpu::X86_64V4),
            Some(cli_backend_name),
        )
        .unwrap();

        assert_eq!(policy.target.arch, simple_common::target::TargetArch::X86_64);
        assert_eq!(policy.cpu, TargetCpu::X86_64V4);
        assert_eq!(policy.backend, cli_backend);
    }

    #[test]
    fn test_resolve_native_build_policy_uses_project_before_user() {
        let project = tempfile::tempdir().unwrap();
        let source = write_project_manifest(
            &project,
            r#"
[compile]
target = "riscv64"
cpu = "default"
backend = "cranelift"
"#,
        );

        let user_home = tempfile::tempdir().unwrap();
        let simple_dir = user_home.path().join(".simple");
        fs::create_dir_all(&simple_dir).unwrap();
        fs::write(
            simple_dir.join("config.toml"),
            r#"
[compile]
target = "aarch64"
cpu = "native"
backend = "llvm"
"#,
        )
        .unwrap();
        let _home = EnvVarGuard::set("HOME", user_home.path());

        let policy = resolve_native_build_policy(&source, None, None, None).unwrap();

        assert_eq!(policy.target.arch, simple_common::target::TargetArch::Riscv64);
        assert_eq!(policy.cpu, TargetCpu::Default);
        assert_eq!(policy.backend, NativeCodegenBackend::Cranelift);
    }

    #[test]
    fn test_resolve_native_build_policy_defaults_to_builtin_backend_and_x86_64_v3_for_host_x86_64() {
        let project = tempfile::tempdir().unwrap();
        let src = project.path().join("main.spl");
        fs::write(&src, "fn main() -> i32:\n    return 0\n").unwrap();

        let policy = resolve_native_build_policy(&src, None, None, None).unwrap();

        assert_eq!(policy.backend, default_native_codegen_backend());
        if policy.target.arch == simple_common::target::TargetArch::X86_64 {
            assert_eq!(policy.cpu, TargetCpu::X86_64V3);
        }
    }

    #[cfg(not(feature = "llvm"))]
    #[test]
    fn test_resolve_native_build_policy_rejects_unavailable_llvm_backend() {
        let project = tempfile::tempdir().unwrap();
        let src = project.path().join("main.spl");
        fs::write(&src, "fn main() -> i32:\n    return 0\n").unwrap();

        let err = resolve_native_build_policy(&src, None, None, Some("llvm")).unwrap_err();
        assert!(err.contains("not available in this build"));
    }

    #[test]
    fn test_parse_native_backend_name_rejects_unknown() {
        let err = parse_native_backend_name("wat").unwrap_err();
        assert!(err.contains("unsupported native backend"));
    }

    #[test]
    fn test_parse_target_flag_equals_form() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--target=wasm32-wasi".to_string(),
        ];
        let target = parse_target_flag(&args).unwrap().unwrap();
        assert_eq!(target.to_string(), "wasm32-wasi");
    }

    #[test]
    fn test_parse_no_target() {
        let args = vec!["compile".to_string(), "test.spl".to_string()];
        let target = parse_target_flag(&args).unwrap();
        assert!(target.is_none());
    }

    #[test]
    fn test_parse_source_arg_allows_flags_before_source() {
        let args = vec![
            "compile".to_string(),
            "--backend=vhdl".to_string(),
            "test.spl".to_string(),
            "-o".to_string(),
            "out.vhd".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }

    #[test]
    fn test_parse_source_arg_skips_output_value() {
        let args = vec![
            "compile".to_string(),
            "-o".to_string(),
            "out.smf".to_string(),
            "--snapshot".to_string(),
            "test.spl".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }

    #[test]
    fn test_parse_opt_level_equals_form() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--opt-level=aggressive".to_string(),
        ];
        let level = parse_opt_level_flag(&args).unwrap();
        assert_eq!(level, Some(NativeOptimizationLevel::Aggressive));
    }

    #[test]
    fn test_parse_opt_level_split_form() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--opt-level".to_string(),
            "basic".to_string(),
        ];
        let level = parse_opt_level_flag(&args).unwrap();
        assert_eq!(level, Some(NativeOptimizationLevel::Basic));
    }

    #[test]
    fn test_parse_source_arg_skips_opt_level_value() {
        let args = vec![
            "compile".to_string(),
            "--opt-level".to_string(),
            "aggressive".to_string(),
            "test.spl".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }

    #[test]
    fn test_parse_source_arg_ignores_no_strip_flag() {
        let args = vec![
            "compile".to_string(),
            "--no-strip".to_string(),
            "test.spl".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }

    #[test]
    fn test_resolve_native_strip_mode_defaults_to_debug_strip_for_host_executables() {
        let mode = resolve_native_strip_mode(&["compile".to_string()], Target::host(), false);
        assert_eq!(mode, NativeStripMode::Debug);
    }

    #[test]
    fn test_resolve_native_strip_mode_honors_no_strip() {
        let mode = resolve_native_strip_mode(
            &["compile".to_string(), "--no-strip".to_string()],
            Target::host(),
            false,
        );
        assert_eq!(mode, NativeStripMode::None);
    }

    #[test]
    fn test_resolve_native_strip_mode_honors_explicit_strip() {
        let mode = resolve_native_strip_mode(
            &["compile".to_string(), "--strip".to_string()],
            Target::host(),
            false,
        );
        assert_eq!(mode, NativeStripMode::All);
    }

    #[test]
    fn test_resolve_native_strip_mode_no_strip_wins_over_strip() {
        let mode = resolve_native_strip_mode(
            &["compile".to_string(), "--strip".to_string(), "--no-strip".to_string()],
            Target::host(),
            false,
        );
        assert_eq!(mode, NativeStripMode::None);
    }

    #[test]
    fn test_resolve_native_strip_mode_does_not_auto_strip_shared_or_cross_targets() {
        let shared = resolve_native_strip_mode(&["compile".to_string()], Target::host(), true);
        let cross = resolve_native_strip_mode(
            &["compile".to_string()],
            Target::parse("aarch64").expect("target"),
            false,
        );
        assert_eq!(shared, NativeStripMode::None);
        assert_eq!(cross, NativeStripMode::None);
    }
}
