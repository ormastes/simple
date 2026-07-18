//! Tests for native project builder.

use std::fs;
use std::path::PathBuf;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use crate::codegen::common_backend::{module_init_symbol, module_prefix_from_path};
use crate::incremental::SourceInfo;
use crate::pipeline::execution::runtime_bundle_env_lock_for_tests as runtime_bundle_env_lock;
use simple_simd::{host_cpu_config, reset_host_cpu_config_cache_for_tests, HostCpuConfig, SimdTier};
use super::*;

#[test]
fn pure_simple_lambda_inline_helper_has_both_callers() {
    let lowering = include_str!("../../../../../compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl");
    let methods = include_str!("../../../../../compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl");
    assert!(lowering.contains("me lower_inline_lambda_with_locals("));
    assert!(lowering.contains("self.lower_inline_lambda_with_locals(params, body, arg_locals)"));
    assert!(methods.contains("self.lower_inline_lambda_with_locals(map_params, map_body, [some_val_map])"));
}

#[test]
fn dim_solver_unit_result_constructor_has_unit_payload() {
    let source = include_str!("../../../../../compiler/30.types/dim_constraints.spl");
    assert!(!source.lines().any(|line| line.trim() == "Ok()"));
}

#[test]
fn test_llvm_project_path_propagates_import_function_arities() {
    let compiler = include_str!("compiler.rs");
    assert!(
        compiler.contains(
            "llvm.set_import_map(imports.import_map.clone());\n            llvm.set_fn_arities(imports.fn_arities.clone());"
        ),
        "LLVM project compilation must install discovered function arities before codegen"
    );
}

fn simd_tier_env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn process_dir_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn archive_members(path: &Path) -> Option<Vec<String>> {
    let tool = find_archive_tool();
    let output = archive_list_command(&tool, path).output().ok()?;
    if !output.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .map(ToOwned::to_owned)
            .collect(),
    )
}

fn command_args(command: &std::process::Command) -> Vec<String> {
    command
        .get_args()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect()
}

#[test]
fn native_object_staging_survives_cache_clean() {
    let root = tempfile::tempdir().unwrap();
    let cache_base_dir = root.path().join("native-cache");
    let cache_dir = cache_base_dir.join("aarch64-unknown-linux-gnu");
    fs::create_dir_all(&cache_dir).unwrap();
    fs::write(cache_dir.join("stale"), b"stale").unwrap();
    fs::remove_dir_all(&cache_base_dir).unwrap();

    let staging = native_object_staging_dir(&cache_base_dir, &cache_dir).unwrap();
    let object = staging.path().join("mod_0.o");
    fs::write(&object, b"object").unwrap();
    assert!(cache_dir.is_dir());
    fs::remove_dir_all(&cache_base_dir).unwrap();

    assert!(!staging.path().starts_with(&cache_base_dir));
    assert_eq!(staging.path().parent(), Some(root.path()));
    assert_eq!(fs::read(object).unwrap(), b"object");
}

#[test]
fn native_object_materialization_retries_the_complete_cached_and_fresh_set() {
    let cache = tempfile::tempdir().unwrap();
    let cached_source = cache.path().join("cached.o");
    std::fs::write(&cached_source, b"cached-object").unwrap();
    let cached_objects = vec![(0usize, cached_source)];
    let fresh_objects = vec![(1usize, b"fresh-object".to_vec())];

    let initial = tempfile::tempdir().unwrap();
    let initial_path = initial.path().to_path_buf();
    let mut removed_initial = false;
    let (replacement, mut all_paths) =
        materialize_native_objects_with_initial_and_hook(initial, &cached_objects, &fresh_objects, |directory| {
            if !removed_initial {
                std::fs::remove_dir_all(directory).unwrap();
                removed_initial = true;
            }
        })
        .unwrap();

    assert!(removed_initial);
    assert_ne!(replacement.path(), initial_path);
    all_paths.sort_by_key(|(index, _)| *index);
    assert_eq!(std::fs::read(&all_paths[0].1).unwrap(), b"cached-object");
    assert_eq!(std::fs::read(&all_paths[1].1).unwrap(), b"fresh-object");
    assert!(all_paths.iter().all(|(_, path)| path.starts_with(replacement.path())));
}

#[test]
fn msvc_lib_archive_commands_use_native_argument_forms() {
    let archive = PathBuf::from("out.lib");
    let objects = vec![PathBuf::from("one.obj"), PathBuf::from("two.obj")];

    let create = archive_create_command("/opt/msvc/lib.exe", &archive, &objects, false, true);
    assert_eq!(command_args(&create), ["/NOLOGO", "/OUT:out.lib", "one.obj", "two.obj"]);

    let append = archive_create_command("lib", &archive, &objects[..1], true, false);
    assert_eq!(command_args(&append), ["/NOLOGO", "/OUT:out.lib", "out.lib", "one.obj"]);

    let list = archive_list_command("lib.exe", &archive);
    assert_eq!(command_args(&list), ["/NOLOGO", "/LIST", "out.lib"]);
}

#[test]
fn llvm_ar_archive_commands_keep_gnu_argument_forms() {
    let archive = PathBuf::from("libout.a");
    let objects = vec![PathBuf::from("one.o")];

    let create = archive_create_command("llvm-ar", &archive, &objects, false, true);
    assert_eq!(command_args(&create), ["rcsD", "libout.a", "one.o"]);

    let append = archive_create_command("llvm-ar", &archive, &objects, true, false);
    assert_eq!(command_args(&append), ["rs", "libout.a", "one.o"]);

    let list = archive_list_command("llvm-ar", &archive);
    assert_eq!(command_args(&list), ["t", "libout.a"]);
}

fn test_host_object_extension() -> &'static str {
    #[cfg(target_os = "windows")]
    {
        "obj"
    }
    #[cfg(not(target_os = "windows"))]
    {
        "o"
    }
}

#[test]
fn hosted_freebsd_cross_target_build_fails_closed() {
    use simple_common::target::{Target, TargetArch, TargetOS};

    let arch = if TargetArch::host() == TargetArch::X86_64 {
        TargetArch::Aarch64
    } else {
        TargetArch::X86_64
    };
    for emit_archive in [false, true] {
        let config = NativeBuildConfig {
            target: Some(Target::new(arch, TargetOS::FreeBSD)),
            emit_archive,
            ..Default::default()
        };
        let error = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/tool"))
            .config(config)
            .build()
            .unwrap_err();

        assert_eq!(
            error,
            "cross-target FreeBSD executable and archive builds are unsupported without a FreeBSD toolchain and sysroot; build on FreeBSD or emit an object instead"
        );
    }
}

#[cfg(target_os = "linux")]
fn build_compiler_backfill_test_archive(root: &Path, name: &str, sources: &[&str]) -> PathBuf {
    let mut objects = Vec::new();
    for (index, source) in sources.iter().enumerate() {
        let source_path = root.join(format!("{name}_{index}.c"));
        let object_path = root.join(format!("{name}_{index}.o"));
        std::fs::write(&source_path, source).unwrap();
        assert!(std::process::Command::new(find_c_compiler())
            .args(["-c", "-ffunction-sections", "-fdata-sections"])
            .arg(&source_path)
            .arg("-o")
            .arg(&object_path)
            .status()
            .unwrap()
            .success());
        objects.push(object_path);
    }
    let archive = root.join(format!("lib{name}.a"));
    let tool = find_archive_tool();
    assert!(archive_create_command(&tool, &archive, &objects, false, false)
        .status()
        .unwrap()
        .success());
    archive
}

#[cfg(target_os = "linux")]
#[test]
fn strip_llvm_constructors_preserves_priority_non_llvm_constructor() {
    let temp = tempfile::tempdir().unwrap();
    let archive = build_compiler_backfill_test_archive(
        temp.path(),
        "constructor_sections",
        &[r#"
__attribute__((constructor)) static void llvm_style_ctor(void) {}
__attribute__((constructor(101))) static void non_llvm_ctor(void) {}
"#],
    );

    let stripped = strip_llvm_constructors(&archive, temp.path()).unwrap();
    let sections = std::process::Command::new("readelf")
        .args(["-SW"])
        .arg(stripped)
        .output()
        .unwrap();
    assert!(sections.status.success());
    let sections = String::from_utf8_lossy(&sections.stdout);
    let names: Vec<&str> = sections.split_whitespace().collect();
    assert!(!names.contains(&".init_array"));
    assert!(names.iter().any(|name| name.starts_with(".init_array.")));
}

#[test]
fn canonical_bootstrap_does_not_force_diagnostic_whole_archive_mode() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir.parent().unwrap().parent().unwrap().parent().unwrap();
    let script = std::fs::read_to_string(repo_root.join("scripts/bootstrap/bootstrap-from-scratch.sh")).unwrap();

    assert!(!script.contains("SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE=1"));
}

#[test]
fn simpleos_freestanding_linker_script_defaults_and_overrides() {
    use simple_common::target::{Target, TargetArch, TargetOS};

    let sysroot = Path::new("/tmp/simpleos-sysroot");
    let simpleos = Target::new(TargetArch::X86_64, TargetOS::SimpleOS);
    let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
    assert_eq!(
        NativeProjectBuilder::resolve_freestanding_linker_script(None, simpleos, sysroot),
        Some(sysroot.join("share/simpleos/simpleos.ld"))
    );
    assert_eq!(
        NativeProjectBuilder::resolve_freestanding_linker_script(Some(Path::new("custom.ld")), simpleos, sysroot),
        Some(PathBuf::from("custom.ld"))
    );
    assert_eq!(
        NativeProjectBuilder::resolve_freestanding_linker_script(None, linux, sysroot),
        None
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_native_all_link_args_include_terminfo() {
    let args = super::tools::terminfo_link_args(simple_common::target::Target::host());
    assert!(args.iter().any(|arg| arg == "-ltinfo"), "terminfo args: {args:?}");
}

fn with_core_c_https_openssl_env<T>(value: Option<&str>, f: impl FnOnce() -> T) -> T {
    let previous = std::env::var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL").ok();
    match value {
        Some(value) => std::env::set_var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL", value),
        None => std::env::remove_var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL"),
    }
    let result = f();
    match previous.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL", value),
        None => std::env::remove_var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL"),
    }
    result
}

fn no_stub_fallback_env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn with_simd_tier_env<T>(value: &str, f: impl FnOnce() -> T) -> T {
    let _guard = simd_tier_env_lock().lock().unwrap();
    let previous = std::env::var("SIMPLE_SIMD_TIER").ok();
    std::env::set_var("SIMPLE_SIMD_TIER", value);
    reset_host_cpu_config_cache_for_tests();
    let result = f();
    reset_host_cpu_config_cache_for_tests();
    match previous.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
        None => std::env::remove_var("SIMPLE_SIMD_TIER"),
    }
    reset_host_cpu_config_cache_for_tests();
    result
}

fn with_simd_envs<T>(simd_tier: Option<&str>, cpu_config_path: Option<&Path>, f: impl FnOnce() -> T) -> T {
    let _guard = simd_tier_env_lock().lock().unwrap();
    let previous_simd_tier = std::env::var("SIMPLE_SIMD_TIER").ok();
    let previous_cpu_config_path = std::env::var("SIMPLE_CPU_CONFIG_PATH").ok();

    match simd_tier {
        Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
        None => std::env::remove_var("SIMPLE_SIMD_TIER"),
    }

    match cpu_config_path {
        Some(path) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", path),
        None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
    }

    reset_host_cpu_config_cache_for_tests();
    let result = f();
    reset_host_cpu_config_cache_for_tests();

    match previous_simd_tier.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
        None => std::env::remove_var("SIMPLE_SIMD_TIER"),
    }

    match previous_cpu_config_path.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", value),
        None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
    }
    reset_host_cpu_config_cache_for_tests();

    result
}

fn render_string_list(values: &[String]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!("\"{value}\""))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn render_tier_list(values: &[SimdTier]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|value| format!("\"{}\"", value.as_str()))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn instruction_sets_for_tier(tier: SimdTier) -> &'static [&'static str] {
    match tier {
        SimdTier::Scalar => &[],
        SimdTier::X86_64Sse2 => &["sse2"],
        SimdTier::X86_64Avx2 => &["sse2", "avx2"],
        SimdTier::X86_64Avx512 => &["sse2", "avx2", "avx512f"],
        SimdTier::Aarch64Neon => &["neon"],
        SimdTier::Aarch64Sve => &["neon", "sve"],
        SimdTier::Aarch64Sve2 => &["neon", "sve", "sve2"],
        SimdTier::Riscv64Rvv => &["rvv"],
        SimdTier::Wasm128 => &["wasm128"],
    }
}

fn config_document(base: &HostCpuConfig, enabled_tier: SimdTier) -> String {
    let enabled_instruction_sets = instruction_sets_for_tier(enabled_tier)
        .iter()
        .filter(|instruction_set| {
            base.simple_support
                .instruction_sets
                .iter()
                .any(|supported| supported == **instruction_set)
        })
        .map(|instruction_set| (*instruction_set).to_string())
        .collect::<Vec<_>>();

    format!(
        concat!(
            "version: 1\n",
            "target_triple: \"{}\"\n",
            "generated_by: \"test\"\n",
            "support:\n",
            "    simd_tier: \"{}\"\n",
            "    instruction_sets: {}\n",
            "simple_support:\n",
            "    simd_tier_fallbacks: {}\n",
            "    instruction_sets: {}\n",
            "enabled:\n",
            "    simd_tier: \"{}\"\n",
            "    instruction_sets: {}\n"
        ),
        base.target_triple,
        base.support.simd_tier.as_str(),
        render_string_list(&base.support.instruction_sets),
        render_tier_list(&base.simple_support.simd_tier_fallbacks),
        render_string_list(&base.simple_support.instruction_sets),
        enabled_tier.as_str(),
        render_string_list(&enabled_instruction_sets),
    )
}

fn with_current_dir<T>(dir: &std::path::Path, f: impl FnOnce() -> T) -> T {
    let _guard = process_dir_lock().lock().unwrap();
    let previous = std::env::current_dir().unwrap();
    std::env::set_current_dir(dir).unwrap();
    let result = f();
    std::env::set_current_dir(previous).unwrap();
    result
}

#[test]
#[ignore = "debug-only closure probe; not a stable regression test"]
fn debug_os_entry_closure() {
    // Navigate from CARGO_MANIFEST_DIR (compiler/) up to repo root
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // manifest_dir = .../src/compiler_rust/compiler
    let project_root = manifest_dir
        .parent()
        .unwrap() // src/compiler_rust
        .parent()
        .unwrap() // src
        .parent()
        .unwrap() // repo root
        .to_path_buf();

    let entry = project_root.join("examples/simple_os/arch/x86_64/os_entry.spl");
    if !entry.exists() {
        eprintln!("entry not found at {}", entry.display());
        return;
    }

    let builder = NativeProjectBuilder::new(project_root.clone(), PathBuf::from("/tmp/x"))
        .source_dir(project_root.join("src/os"))
        .entry_file(entry.clone());

    let files = builder.discover_reachable_files_with_sources(&entry).unwrap();
    eprintln!("=== {} files discovered ===", files.len());
    for (p, _) in &files {
        let ps = p.to_string_lossy();
        if ps.contains("shell_app")
            || ps.contains("/vfs")
            || ps.contains("terminal")
            || ps.contains("hello_world")
            || ps.contains("fs_types")
        {
            eprintln!("  {}", p.display());
        }
    }
    panic!("see stderr above");
}

#[test]
fn repo_native_discovery_sources_parse() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    for relative in [
        "src/app/io/_CliCompile/compile_targets.spl",
        "src/lib/common/encoding/sfnt.spl",
        "src/lib/common/encoding/sfnt_glyf.spl",
        "src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl",
    ] {
        let path = repo_root.join(relative);
        let source = std::fs::read_to_string(&path).unwrap();
        simple_parser::Parser::new(&source)
            .parse()
            .unwrap_or_else(|error| panic!("{} {:?}: {error}", path.display(), error.span()));
    }
}

#[test]
fn test_module_prefix_from_path() {
    let source_root = PathBuf::from("/project/src");

    assert_eq!(
        module_prefix_from_path(
            &PathBuf::from("/project/src/compiler/10.frontend/core/lexer.spl"),
            &source_root
        ),
        "compiler__frontend__core__lexer"
    );

    assert_eq!(
        module_prefix_from_path(&PathBuf::from("/project/src/app/cli/main.spl"), &source_root),
        "app__cli__main"
    );

    assert_eq!(
        module_prefix_from_path(&PathBuf::from("/project/src/lib/common/text.spl"), &source_root),
        "lib__common__text"
    );

    assert_eq!(
        module_prefix_from_path(&PathBuf::from("/project/src/app/ui.render/ansi.spl"), &source_root),
        "app__ui.render__ansi"
    );

    assert_eq!(
        module_prefix_from_path(
            &PathBuf::from("/project/test/01_unit/lib/nogc_async_mut/concurrent_wrappers_spec.spl"),
            &PathBuf::from("/project/test")
        ),
        "m_01_unit__lib__nogc_async_mut__concurrent_wrappers_spec"
    );
}

#[test]
fn test_dotted_module_init_symbol_matches_portable_c_reference() {
    assert_eq!(
        module_init_symbol(Some("app__ui.render__ansi")),
        "__module_init_app__ui_dot_render__ansi"
    );
    assert_eq!(module_init_symbol(None), "__module_init");
}

#[test]
fn test_collect_spl_files() {
    let temp = tempfile::tempdir().unwrap();
    let dir = temp.path();
    std::fs::write(dir.join("a.spl"), "# test").unwrap();
    std::fs::write(dir.join("b.txt"), "not spl").unwrap();
    std::fs::create_dir(dir.join("sub")).unwrap();
    std::fs::write(dir.join("sub/c.spl"), "# test").unwrap();

    let mut files = Vec::new();
    collect_spl_files_recursive(dir, &mut files);
    assert_eq!(files.len(), 2);
}

#[test]
fn test_content_hash_consistency() {
    let h1 = content_hash("fn main(): return 42");
    let h2 = content_hash("fn main(): return 42");
    assert_eq!(h1, h2);

    let h3 = content_hash("fn main(): return 0");
    assert_ne!(h1, h3);
}

#[test]
fn test_content_hash_matches_source_info() {
    let content = "fn main(): return 42";
    let hash = content_hash(content);

    let mut info = SourceInfo::new(PathBuf::from("test.spl"));
    info.update_from_content(content);

    assert_eq!(hash, info.content_hash);
}

#[test]
fn test_security_registry_init_source_filters_and_escapes() {
    assert!(source_may_declare_security(
        "security gate UserAdminGate:\n    from feature user\n"
    ));
    assert!(source_may_declare_security("security AppSecurity:\n    default deny\n"));
    assert!(source_may_declare_security(
        "capability ReadReports:\n    resource Dir\n"
    ));
    assert!(!source_may_declare_security(
        "# security note\nclass UserService:\n    pass\n"
    ));
    assert!(!source_may_declare_security("class UserService:\n    pass\n"));

    let escaped = cxx_raw_string_literal("before )SECURITY_SDN\" after");
    assert!(!escaped.contains(")SECURITY_SDN\""));
}

#[test]
fn test_security_registry_embeds_sandbox_lowering_metadata() {
    let source = r#"security gate PluginGate:
    sandbox plugin_sandbox
    grant:
        ReadDir["/reports"]

sandbox plugin_sandbox:
    backend simple_os
    net deny all
"#;
    let file_sources = vec![(PathBuf::from("src/security/gate/plugin_gate.spl"), source.to_string())];
    let registry = security_registry_sdn_from_sources(&file_sources)
        .expect("security registry generation should parse")
        .expect("security source should produce a registry");
    assert!(registry.contains("security_aop_lowering:"));
    assert!(registry.contains("sandbox_lowering:"));
    assert!(registry.contains("plugin_sandbox:"));
    assert!(registry.contains("lowered_backend: simple_os_native_object_capability_handles"));
    assert!(registry.contains("- ReadDir[\"/reports\"]"));
}

#[test]
fn test_object_cache_key_separates_simd_tiers() {
    let scalar = with_simd_tier_env("scalar", || {
        object_cache_key("fn main(): return 42", true, "cranelift", false, "app__main")
    });
    let avx2 = with_simd_tier_env("x86_64_avx2", || {
        object_cache_key("fn main(): return 42", true, "cranelift", false, "app__main")
    });

    assert_ne!(scalar, avx2);
}

#[test]
fn test_object_cache_key_separates_configured_active_tiers_without_override() {
    let temp = tempfile::tempdir().unwrap();
    let base_path = temp.path().join("cpu_config.sdn");
    let detected = with_simd_envs(None, Some(&base_path), || host_cpu_config().unwrap());
    let configured_tiers = &detected.simple_support.simd_tier_fallbacks;
    let Some(high_tier) = configured_tiers.first().copied() else {
        panic!("host config did not expose any supported SIMD tiers");
    };
    let Some(low_tier) = configured_tiers.iter().rev().copied().find(|tier| *tier != high_tier) else {
        return;
    };

    let high_path = temp.path().join("high_cpu_config.sdn");
    let low_path = temp.path().join("low_cpu_config.sdn");
    fs::write(&high_path, config_document(&detected, high_tier)).unwrap();
    fs::write(&low_path, config_document(&detected, low_tier)).unwrap();

    let high_active = with_simd_envs(None, Some(&high_path), crate::stdlib_variant::active_simd_tier_name);
    let low_active = with_simd_envs(None, Some(&low_path), crate::stdlib_variant::active_simd_tier_name);

    assert_ne!(high_tier, low_tier);
    if high_active == low_active {
        return;
    }

    let high = with_simd_envs(None, Some(&high_path), || {
        object_cache_key("fn main(): return 42", true, "cranelift", false, "app__main")
    });
    let low = with_simd_envs(None, Some(&low_path), || {
        object_cache_key("fn main(): return 42", true, "cranelift", false, "app__main")
    });

    assert_ne!(high, low);
}

#[test]
fn test_compiler_fingerprint_is_stable_within_process() {
    // The fingerprint is cached in a OnceLock, so repeated calls in the same
    // process (same running exe) must return the exact same value -- this is
    // what keeps cache hits working across repeated builds with an unchanged
    // compiler binary.
    let a = compiler_fingerprint();
    let b = compiler_fingerprint();
    assert_eq!(a, b);
}

#[test]
fn test_object_cache_key_includes_compiler_fingerprint() {
    // Reproduce the pre-fix key formula (content, is_entry, backend, no_mangle,
    // module_prefix, SIMPLE_NATIVE_CPU, simd tier -- no compiler fingerprint)
    // and confirm the real key differs because the fingerprint is folded in.
    // Without this, a seed codegen fix that doesn't touch any .spl source text
    // would silently keep reusing objects built by the old binary.
    use std::hash::{Hash, Hasher};
    let content = "fn main(): return 42";
    let is_entry = true;
    let backend = "cranelift";
    let no_mangle = false;
    let module_prefix = "app__main";

    let mut legacy_hasher = std::collections::hash_map::DefaultHasher::new();
    content.hash(&mut legacy_hasher);
    is_entry.hash(&mut legacy_hasher);
    backend.hash(&mut legacy_hasher);
    no_mangle.hash(&mut legacy_hasher);
    module_prefix.hash(&mut legacy_hasher);
    std::env::var("SIMPLE_NATIVE_CPU")
        .unwrap_or_default()
        .hash(&mut legacy_hasher);
    active_simd_tier_name().hash(&mut legacy_hasher);
    let legacy_key = legacy_hasher.finish();

    let real_key = object_cache_key(content, is_entry, backend, no_mangle, module_prefix);

    // A real process's compiler_fingerprint() is a SipHash over actual exe
    // bytes (or exe metadata), astronomically unlikely to be exactly zero,
    // so folding it in must change the key relative to the legacy formula.
    assert_ne!(
        real_key, legacy_key,
        "object_cache_key must differ from the pre-fingerprint formula, or a \
         rebuilt compiler binary would silently reuse stale cached objects"
    );

    // Cache hits for an unchanged binary must still work: identical inputs in
    // the same process produce identical keys.
    let real_key_again = object_cache_key(content, is_entry, backend, no_mangle, module_prefix);
    assert_eq!(real_key, real_key_again);
}

#[test]
fn test_incremental_cache_dir_default() {
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"));
    let cache_dir = builder.cache_dir().to_string_lossy().replace('\\', "/");
    assert!(cache_dir.ends_with("/project/.simple/native_cache"));
}

#[test]
fn test_source_dir_preserves_logical_path() {
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"))
        .source_dir(PathBuf::from("src/app/mcp_t32"));
    let source_dir = builder.source_dirs[0].to_string_lossy().replace('\\', "/");
    assert!(source_dir.ends_with("/project/src/app/mcp_t32"));
}

#[test]
fn test_inline_asm_cache_guard_ignores_compiler_metadata_mentions() {
    let source = r#"
# inline asm in comments is not an emitted sidecar
fn lower_inline_asm_name() -> text:
    "InlineAsm"
"#;
    assert!(!source_may_emit_inline_asm_sidecar(source));
}

#[test]
fn test_inline_asm_cache_guard_detects_real_inline_asm_syntax() {
    assert!(source_may_emit_inline_asm_sidecar("fn f():\n    asm { nop }\n"));
    assert!(source_may_emit_inline_asm_sidecar("fn f():\n    asm(\"nop\")\n"));
    assert!(source_may_emit_inline_asm_sidecar(
        "fn f():\n    asm volatile { nop }\n"
    ));
}

#[test]
fn test_native_hir_resolver_roots_include_project_src_for_narrow_sources() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    std::fs::create_dir_all(project_root.join("src/os/kernel/types")).unwrap();
    std::fs::create_dir_all(project_root.join("src/lib")).unwrap();
    std::fs::create_dir_all(project_root.join("examples/simple_os")).unwrap();

    let roots = native_hir_resolver_roots(
        &project_root,
        &[
            project_root.join("src/os"),
            project_root.join("src/lib"),
            project_root.join("examples/simple_os"),
        ],
    );

    assert!(roots
        .iter()
        .any(|root| root == &safe_canonicalize(&project_root.join("src"))));
    assert!(roots
        .iter()
        .any(|root| root == &safe_canonicalize(&project_root.join("src/os"))));
    assert!(roots
        .iter()
        .any(|root| root == &safe_canonicalize(&project_root.join("src/lib"))));
    assert!(roots
        .iter()
        .any(|root| root == &safe_canonicalize(&project_root.join("examples/simple_os"))));
}

#[test]
fn test_incremental_cache_dir_custom() {
    let config = NativeBuildConfig {
        cache_dir: Some(PathBuf::from("/tmp/my_cache")),
        ..Default::default()
    };

    let builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple")).config(config);

    assert_eq!(builder.cache_dir(), PathBuf::from("/tmp/my_cache"));
}

#[test]
fn test_default_config_mangle() {
    let config = NativeBuildConfig::default();
    assert!(
        !config.no_mangle,
        "no_mangle should default to false (mangling enabled)"
    );
    assert!(config.incremental, "incremental should default to true");
    assert!(!config.clean, "clean should default to false");
}

#[test]
fn test_discover_files_includes_explicit_entry_outside_source_dirs() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    let tools_dir = project_root.join("examples/tool");
    std::fs::create_dir_all(&src_dir).unwrap();
    std::fs::create_dir_all(&tools_dir).unwrap();

    let lib_file = src_dir.join("lib.spl");
    let entry_file = tools_dir.join("main.spl");
    std::fs::write(&lib_file, "fn helper(): pass").unwrap();
    std::fs::write(&entry_file, "fn main(): pass").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry_file.clone());

    let files = builder.discover_files().unwrap();
    assert!(!files.iter().any(|path| same_file_path(path, &lib_file)));
    assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
    assert_eq!(files.len(), 1);
}

#[test]
fn test_discover_files_from_entry_excludes_unrelated_source_files() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_app_dir = project_root.join("src/app/mcp_t32");
    let examples_dir = project_root.join("examples/tool");
    std::fs::create_dir_all(&src_app_dir).unwrap();
    std::fs::create_dir_all(&examples_dir).unwrap();

    let helper_file = src_app_dir.join("helper.spl");
    let unrelated_file = project_root.join("src/unrelated.spl");
    let entry_file = examples_dir.join("main.spl");

    std::fs::write(&helper_file, "fn helper() -> i64:\n    return 1\n").unwrap();
    std::fs::write(&unrelated_file, "fn unrelated() -> i64:\n    return 2\n").unwrap();
    std::fs::write(
        &entry_file,
        "use app.mcp_t32.helper\nfn main() -> i64:\n    return helper()\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(project_root.join("src"))
        .entry_file(entry_file.clone());

    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
    assert!(files.iter().any(|path| same_file_path(path, &helper_file)));
    assert!(!files.iter().any(|path| same_file_path(path, &unrelated_file)));
    assert_eq!(files.len(), 2);
}

#[test]
fn test_entry_closure_handles_shared_import_fan_in() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_app_dir = project_root.join("src/app");
    let src_lib_dir = project_root.join("src/lib");
    std::fs::create_dir_all(&src_app_dir).unwrap();
    std::fs::create_dir_all(&src_lib_dir).unwrap();

    let entry_file = src_app_dir.join("main.spl");
    let a_file = src_lib_dir.join("a.spl");
    let b_file = src_lib_dir.join("b.spl");
    let shared_file = src_lib_dir.join("shared.spl");
    let shadow_file = src_app_dir.join("lib/shared.spl");
    std::fs::create_dir_all(shadow_file.parent().unwrap()).unwrap();

    std::fs::write(
        &entry_file,
        "use lib.a.{a}\nuse lib.b.{b}\nfn main() -> i64:\n    return a() + b()\n",
    )
    .unwrap();
    std::fs::write(&a_file, "use lib.shared.{s}\nfn a() -> i64:\n    return s()\n").unwrap();
    std::fs::write(&b_file, "use lib.shared.{s}\nfn b() -> i64:\n    return s()\n").unwrap();
    std::fs::write(&shared_file, "fn s() -> i64:\n    return 1\n").unwrap();
    std::fs::write(&shadow_file, "fn s() -> i64:\n    return 2\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_app_dir)
        .source_dir(src_lib_dir)
        .entry_file(entry_file.clone());

    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
    assert!(files.iter().any(|path| same_file_path(path, &a_file)));
    assert!(files.iter().any(|path| same_file_path(path, &b_file)));
    assert!(files.iter().any(|path| same_file_path(path, &shared_file)));
    assert!(!files.iter().any(|path| same_file_path(path, &shadow_file)));
    assert_eq!(files.len(), 4);
}

#[test]
fn test_entry_closure_follows_function_local_imports() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(src_dir.join("lib")).unwrap();
    let entry = src_dir.join("app/main.spl");
    let helper = src_dir.join("lib/helper.spl");
    std::fs::write(&entry, "fn main():\n    use lib.helper.{value}\n    print value()\n").unwrap();
    std::fs::write(&helper, "fn value() -> i64:\n    1\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &helper)));
}

#[test]
fn test_entry_closure_expands_bare_export_package_facades() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    let package = src_dir.join("lib/facade");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(&package).unwrap();
    let entry = src_dir.join("app/main.spl");
    let init = package.join("__init__.spl");
    let implementation = package.join("serializer.spl");
    let unrelated = package.join("unrelated.spl");
    std::fs::write(&entry, "use lib.facade.{encode}\nfn main():\n    print encode()\n").unwrap();
    std::fs::write(&init, "export encode\n").unwrap();
    std::fs::write(&implementation, "fn encode() -> text:\n    \"ok\"\n").unwrap();
    std::fs::write(&unrelated, "fn decode() -> text:\n    \"no\"\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &init)));
    assert!(files.iter().any(|path| same_file_path(path, &implementation)));
    assert!(!files.iter().any(|path| same_file_path(path, &unrelated)));
    assert_eq!(files.len(), 3);
}

#[test]
fn test_entry_closure_follows_bare_export_facade_to_owner_only() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    let package = src_dir.join("lib/facade");
    let owner_package = src_dir.join("lib/owner");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(&package).unwrap();
    std::fs::create_dir_all(&owner_package).unwrap();
    let entry = src_dir.join("app/main.spl");
    let init = package.join("__init__.spl");
    let facade = package.join("mod.spl");
    let aliased = package.join("aliased.spl");
    let owner = owner_package.join("mod.spl");
    let unrelated = package.join("unrelated.spl");
    std::fs::write(&entry, "use lib.facade.{encode}\nfn main():\n    print encode()\n").unwrap();
    std::fs::write(&init, "export encode\n").unwrap();
    std::fs::write(&facade, "export use lib.owner.mod.{encode}\n").unwrap();
    std::fs::write(&aliased, "export use lib.owner.mod.{encode as renamed}\n").unwrap();
    std::fs::write(&owner, "fn encode() -> text:\n    \"ok\"\n").unwrap();
    std::fs::write(&unrelated, "fn decode() -> text:\n    \"no\"\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &init)));
    assert!(files.iter().any(|path| same_file_path(path, &facade)));
    assert!(files.iter().any(|path| same_file_path(path, &owner)));
    assert!(!files.iter().any(|path| same_file_path(path, &aliased)));
    assert!(!files.iter().any(|path| same_file_path(path, &unrelated)));
    assert_eq!(files.len(), 4);
}

// Regression coverage for the `frontend_core` false-ambiguous-export bug
// (doc/08_tracking/bug/frontend_core_ambiguous_export_regression_2026-07-13.md):
// a stale `extern fn` re-declaration of an already-defined symbol must not
// tie against the real definition and must not fail discovery. Real
// same-name-different-symbol collisions must still be rejected.
#[test]
fn test_entry_closure_bare_export_prefers_definition_over_stale_extern() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    let package = src_dir.join("pkg");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(&package).unwrap();
    let entry = src_dir.join("app/main.spl");
    let init = package.join("__init__.spl");
    let owner = package.join("owner.spl");
    let stale = package.join("stale.spl");
    std::fs::write(
        &entry,
        "use pkg.{get_members}\nfn main() -> i64:\n    return get_members()\n",
    )
    .unwrap();
    std::fs::write(&init, "export get_members\n").unwrap();
    std::fs::write(&owner, "fn get_members() -> i64:\n    return 1\n").unwrap();
    // Stale forward declaration of the same symbol: a real fn already
    // defines it elsewhere in the package, so this extern must be treated
    // as a weak re-declaration, not a second provider.
    std::fs::write(
        &stale,
        "extern fn get_members() -> i64\nfn use_it() -> i64:\n    return get_members()\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let files = builder
        .discover_files()
        .expect("stale extern re-declaration must not be flagged as an ambiguous package export");
    assert!(files.iter().any(|path| same_file_path(path, &init)));
    assert!(files.iter().any(|path| same_file_path(path, &owner)));
}

// Verifies the REAL production package named in the bug doc
// (src/compiler/10.frontend/core, module path `compiler.core`) discovers
// cleanly with no false ambiguous-export error, exercising the exact
// resolver/tiering path native-build uses in production against the
// actual ~450-export `__init__.spl` and its 48 sibling files.
#[test]
fn test_entry_closure_real_frontend_core_package_has_no_ambiguous_export() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent() // src/compiler_rust
        .unwrap()
        .parent() // src
        .unwrap()
        .parent() // repo root
        .unwrap()
        .to_path_buf();
    let core_init = repo_root.join("src/compiler/10.frontend/core/__init__.spl");
    assert!(
        core_init.is_file(),
        "expected real frontend core package at {}",
        core_init.display()
    );

    let temp = tempfile::tempdir().unwrap();
    let entry = temp.path().join("entry.spl");
    std::fs::write(
        &entry,
        "use compiler.core.{is_alpha}\nfn main() -> bool:\n    return is_alpha(\"a\")\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(repo_root.clone(), temp.path().join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(repo_root.join("src"))
        .entry_file(entry);
    let files = builder
        .discover_files()
        .expect("real src/compiler/10.frontend/core package must resolve without a false ambiguous-export error");
    assert!(files.iter().any(|path| same_file_path(path, &core_init)));
}

#[test]
fn test_entry_closure_bare_export_rejects_genuine_duplicate_definitions() {
    // Guard against the SIMPLE_AMBIGUOUS_EXPORT_ALL escape hatch (discovery.rs)
    // downgrading this to a warning if it happens to be set in the test process.
    let previous_escape_hatch = std::env::var("SIMPLE_AMBIGUOUS_EXPORT_ALL").ok();
    std::env::remove_var("SIMPLE_AMBIGUOUS_EXPORT_ALL");

    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    let package = src_dir.join("pkg2");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(&package).unwrap();
    let entry = src_dir.join("app/main.spl");
    let init = package.join("__init__.spl");
    let a = package.join("a.spl");
    let b = package.join("b.spl");
    std::fs::write(&entry, "use pkg2.{helper}\nfn main() -> i64:\n    return helper()\n").unwrap();
    std::fs::write(&init, "export helper\n").unwrap();
    // Two genuinely different symbols happen to share a name: this must
    // still fail loudly rather than silently pick one.
    std::fs::write(&a, "fn helper() -> i64:\n    return 1\n").unwrap();
    std::fs::write(&b, "fn helper() -> i64:\n    return 2\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let error = builder
        .discover_files()
        .expect_err("two real definitions of the same exported name must still be rejected as ambiguous");
    match previous_escape_hatch {
        Some(value) => std::env::set_var("SIMPLE_AMBIGUOUS_EXPORT_ALL", value),
        None => std::env::remove_var("SIMPLE_AMBIGUOUS_EXPORT_ALL"),
    }
    assert!(error.contains("ambiguous package export"), "unexpected error: {error}");
    assert!(error.contains("helper"), "unexpected error: {error}");
}

#[test]
fn test_entry_closure_follows_extend_method_imports() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    std::fs::create_dir_all(src_dir.join("app")).unwrap();
    std::fs::create_dir_all(src_dir.join("lib")).unwrap();
    let entry = src_dir.join("app/main.spl");
    let extension = src_dir.join("lib/extended.spl");
    let helper = src_dir.join("lib/helper.spl");
    std::fs::write(&entry, "use lib.extended.*\nfn main():\n    pass\n").unwrap();
    std::fs::write(
        &extension,
        "extend Widget:\n    fn value():\n        use lib.helper.{helper}\n        helper()\n",
    )
    .unwrap();
    std::fs::write(&helper, "fn helper():\n    pass\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(src_dir)
        .entry_file(entry);
    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &extension)));
    assert!(files.iter().any(|path| same_file_path(path, &helper)));
}

#[test]
fn test_entry_closure_resolves_project_src_imports_from_narrow_source_roots() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_os_dir = project_root.join("src/os/kernel/arch/x86_32");
    let examples_dir = project_root.join("examples/simple_os/arch/x86_32");
    std::fs::create_dir_all(&src_os_dir).unwrap();
    std::fs::create_dir_all(&examples_dir).unwrap();

    let dep_file = src_os_dir.join("interrupt.spl");
    let entry_file = examples_dir.join("main.spl");
    std::fs::write(&dep_file, "fn x86_32_install_bootstrap_runtime(cap: u64): pass").unwrap();
    std::fs::write(
        &entry_file,
        "use os.kernel.arch.x86_32.interrupt.{x86_32_install_bootstrap_runtime}\nfn main():\n    x86_32_install_bootstrap_runtime(8)\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(examples_dir.clone())
        .entry_file(entry_file.clone());

    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
    assert!(files.iter().any(|path| same_file_path(path, &dep_file)));
    assert_eq!(files.len(), 2);
}

#[test]
fn test_bootstrap_entry_closure_avoids_driver_package_hub() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let entry = repo_root.join("src/app/cli/bootstrap_main.spl");
    let builder = NativeProjectBuilder::new(repo_root.clone(), repo_root.join("bin/bootstrap-test"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(repo_root.join("src/compiler"))
        .source_dir(repo_root.join("src/app"))
        .source_dir(repo_root.join("src/lib"))
        .entry_file(entry.clone());

    let files = builder.discover_files().unwrap();
    assert!(files
        .iter()
        .any(|path| same_file_path(path, &repo_root.join("src/compiler/80.driver/driver.spl"))));
    assert!(files
        .iter()
        .any(|path| same_file_path(path, &repo_root.join("src/compiler/80.driver/watcher/smf_manifest.spl"))));
    assert!(!files
        .iter()
        .any(|path| same_file_path(path, &repo_root.join("src/compiler/80.driver/__init__.spl"))));
    assert!(!files
        .iter()
        .any(|path| path.starts_with(repo_root.join("src/app/llm_caret"))));
    assert!(!files
        .iter()
        .any(|path| path.starts_with(repo_root.join("src/app/leak_finder"))));
    assert!(!files
        .iter()
        .any(|path| path.starts_with(repo_root.join("src/compiler_rust/lib/std/src"))));
}

#[test]
fn test_discover_files_from_entry_uses_matching_source_root() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let examples_root = project_root.join("examples/tooling");
    let package_dir = examples_root.join("t32_mcp");
    std::fs::create_dir_all(&package_dir).unwrap();

    let entry_file = package_dir.join("main.spl");
    let dep_file = package_dir.join("protocol.spl");

    std::fs::write(&dep_file, "fn ping() -> text:\n    return \"pong\"\n").unwrap();
    std::fs::write(
        &entry_file,
        "use t32_mcp.protocol.{ping}\nfn main() -> text:\n    return ping()\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool"))
        .config(NativeBuildConfig {
            entry_closure: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(examples_root)
        .entry_file(entry_file.clone());

    let files = builder.discover_files().unwrap();
    assert!(files.iter().any(|path| same_file_path(path, &entry_file)));
    assert!(files.iter().any(|path| same_file_path(path, &dep_file)));
    assert_eq!(files.len(), 2);
}

#[test]
fn test_runtime_bundle_auto_prefers_core_c_bootstrap_for_non_compiler_entry_when_simple_core_is_absent() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/t32_mcp_native"))
            .config(config);
    builder.entry_file = Some(PathBuf::from(
        "/project/examples/10_tooling/trace32_tools/t32_mcp/frontend_light.spl",
    ));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_ne!(selected, runtime);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_auto_prefers_core_c_for_compiler_entry() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };

    let mut builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple_native"))
        .config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/main.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_ne!(selected, runtime);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    assert!(!is_native_all);
}

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
#[test]
fn test_runtime_path_cli_archive_does_not_require_optional_lifecycle_hooks() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("runtime.c");
    let object = temp.path().join("runtime.o");
    let runtime = temp.path().join("libsimple_runtime.a");
    std::fs::write(
        &source,
        r#"
void rt_get_args(void) {}
void rt_cli_get_args(void) {}
void rt_array_len(void) {}
void rt_array_get(void) {}
void rt_array_get_text(void) {}
void rt_string_len(void) {}
void rt_string_data(void) {}
void rt_file_read_text(void) {}
void rt_process_run(void) {}
"#,
    )
    .unwrap();
    assert!(std::process::Command::new(find_c_compiler())
        .arg("-c")
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .status()
        .unwrap()
        .success());
    let tool = find_archive_tool();
    assert!(
        archive_create_command(&tool, &runtime, std::slice::from_ref(&object), false, false)
            .status()
            .unwrap()
            .success()
    );

    let config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    let mut builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple_native"))
        .config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/main.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_eq!(selected, runtime);
    assert!(!is_native_all);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
}

#[test]
fn test_runtime_bundle_auto_prefers_core_c_for_compiler_source_root() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };

    let mut builder = NativeProjectBuilder::new(
        PathBuf::from("/project"),
        PathBuf::from("/project/bin/simple_lsp_mcp_server"),
    )
    .config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/simple_lsp_mcp/main.spl"));
    builder.source_dirs.push(PathBuf::from("/project/src/compiler"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_ne!(selected, runtime);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_auto_falls_back_to_core_c_when_simple_core_is_incomplete() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let simple_core_dir = temp.path().join("simple-core");
    std::fs::create_dir_all(&simple_core_dir).unwrap();
    let simple_core = simple_core_dir.join("libsimple_runtime.a");
    let runtime = temp.path().join("libsimple_runtime.a");
    std::fs::write(&simple_core, b"simple-core").unwrap();
    std::fs::write(&runtime, b"core-c").unwrap();

    let config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/hello_native")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/demo/app.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_ne!(selected, runtime);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    assert!(!is_native_all);
}

#[test]
fn test_core_lane_runtime_archives_expose_required_abi_symbols() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();

    let core_c = with_core_c_https_openssl_env(None, || {
        build_core_c_runtime_library(temp.path()).expect("core-c runtime archive should build")
    });
    let core_c_symbols = archive_defined_symbols(&core_c).expect("core-c runtime symbols should be readable");
    let missing = simple_common::CORE_REQUIRED_RUNTIME_SYMBOLS
        .iter()
        .filter(|symbol| !core_c_symbols.contains(symbol.trim_start_matches('_')))
        .copied()
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty() && runtime_archive_has_core_required_symbols(&core_c),
        "core-c runtime archive is missing core-required ABI symbols: {missing:?} ({})",
        core_c.display(),
    );
    assert!(
        core_c_symbols.contains("simd_text_init"),
        "core-c runtime archive must include runtime_simd_utf8.c because runtime_native.c calls simd_text_init"
    );
    assert!(
        core_c_symbols.contains("rt_thread_available_parallelism"),
        "core-c runtime archive must include the thread parallelism ABI used by std.thread_sffi"
    );
    assert!(
        core_c_symbols.contains("spl_thread_cpu_count"),
        "core-c runtime archive must include the legacy thread CPU-count ABI used by std.thread_sffi"
    );
    assert!(core_c_symbols.contains("rt_crc32_text"));
    assert!(core_c_symbols.contains("rt_file_create_excl"));
    assert!(core_c_symbols.contains("rt_file_sync"));
    assert!(core_c_symbols.contains("rt_bytes_alloc"));
    for symbol in [
        "rt_getpid",
        "rt_process_wait",
        "rt_process_run_timeout",
        "rt_string_rfind",
    ] {
        assert!(core_c_symbols.contains(symbol), "core-c runtime must own `{symbol}`");
    }
    assert!(core_c_symbols.contains("rt_invlpg"));
    assert!(core_c_symbols.contains("serial_println"));
    assert!(core_c_symbols.contains("unsafe_addr_of"));
    if effective_target().os == simple_common::target::TargetOS::Linux {
        for symbol in [
            "rt_cocoa_window_new",
            "rt_cocoa_layer_create",
            "rt_cocoa_layer_blend_rect",
            "rt_cocoa_layer_blur",
            "rt_cocoa_layer_gradient_v",
            "rt_win32_window_new",
            "rt_win32_dib_create",
            "rt_win32_dib_present_rect",
        ] {
            assert!(
                core_c_symbols.contains(symbol),
                "Linux core-C runtime must own hosted fallback `{symbol}`"
            );
        }
    }
    for symbol in [
        "rt_array_concat",
        "rt_is_none",
        "rt_math_pow",
        "rt_memory_barrier",
        "rt_read_cr3",
        "rt_read_cr3_raw",
        "rt_volatile_read_u8",
        "rt_volatile_read_u16",
        "rt_volatile_read_u32",
        "rt_volatile_read_u64",
        "rt_volatile_write_u8",
        "rt_volatile_write_u16",
        "rt_volatile_write_u32",
        "rt_volatile_write_u64",
        "rt_write_cr3",
        "rt_write_cr3_raw",
    ] {
        assert!(
            core_c_symbols.contains(symbol),
            "core-c runtime archive missing {symbol}"
        );
    }
    for symbol in simple_common::RUNTIME_SYMBOL_NAMES
        .iter()
        .copied()
        .filter(|symbol| symbol.starts_with("rt_host_gpu_queue_"))
    {
        assert!(
            core_c_symbols.contains(symbol),
            "core-c runtime archive must own the Engine2D queue symbol {symbol}"
        );
    }
    let core_c_members = archive_members(&core_c).expect("core-c runtime archive members should be readable");
    let directx_object = format!("runtime_directx_core.{}", test_host_object_extension());
    assert!(
        core_c_members.contains(&directx_object),
        "core-c runtime archive must include the fail-closed DirectX capsule"
    );
    assert!(core_c_symbols.contains("rt_directx_execute_readback_checked"));
    assert!(core_c_symbols.contains("rt_directx_hardware_adapter_identity"));
    let process_object = format!("runtime_process.{}", test_host_object_extension());
    assert!(
        core_c_members.contains(&process_object),
        "core-c runtime archive must include the process timeout provider"
    );
    assert!(core_c_symbols.contains("rt_process_run_timeout"));
    for provider in ["runtime_fork", "runtime_memtrack"] {
        let object = format!("{provider}.{}", test_host_object_extension());
        assert!(
            core_c_members.contains(&object),
            "core-c runtime archive must include {provider}"
        );
    }
    for symbol in ["rt_fork_child_setup", "rt_fork_parent_wait", "rt_fork_parent_stdout"] {
        assert!(core_c_symbols.contains(symbol), "core-c runtime must own `{symbol}`");
    }
    let https_object = format!("runtime_https_openssl_core.{}", test_host_object_extension());
    assert!(
        !core_c_members.contains(&https_object),
        "core-c runtime archive should not retain hosted OpenSSL/HTTPS by default"
    );

    let https_temp = tempfile::tempdir().unwrap();
    let core_c_with_https = with_core_c_https_openssl_env(Some("1"), || {
        build_core_c_runtime_library(https_temp.path()).expect("core-c HTTPS runtime archive should build")
    });
    let core_c_https_members =
        archive_members(&core_c_with_https).expect("core-c HTTPS runtime archive members should be readable");
    assert!(
        core_c_https_members.contains(&https_object),
        "SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL=1 should include the hosted OpenSSL/HTTPS capsule"
    );

    if let Some(simple_core) = find_abi_complete_simple_core_runtime_library() {
        assert!(
            runtime_archive_has_core_required_symbols(&simple_core),
            "discovered simple-core runtime archive is not ABI-complete: {}",
            simple_core.display()
        );
    }
}

#[test]
fn test_stage4_c_runtime_archive_includes_hosted_font_and_sqlite() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let archive = build_stage4_c_runtime_library(temp.path()).expect("Stage 4 C runtime archive should build");
    let symbols = archive_defined_symbols(&archive).expect("Stage 4 C runtime symbols should be readable");
    assert!(symbols.contains("rt_font_glyph_bitmap"));
    assert!(symbols.contains("rt_sqlite_open"));
    assert!(symbols.contains("spl_memtrack_enable"));
    assert!(symbols.contains("spl_memtrack_disable"));
    assert!(symbols.contains("spl_memtrack_snapshot"));
    assert!(symbols.contains("spl_memtrack_dump_since"));
}

#[test]
fn test_runtime_inputs_fingerprint_tracks_names_and_content() {
    let temp = tempfile::tempdir().unwrap();
    std::fs::write(temp.path().join("runtime.c"), b"one").unwrap();
    std::fs::write(temp.path().join("runtime.h"), b"header").unwrap();

    let initial = runtime_inputs_fingerprint(temp.path(), &["runtime.c", "runtime.h"]).unwrap();
    std::fs::write(temp.path().join("runtime.c"), b"two").unwrap();
    let changed_content = runtime_inputs_fingerprint(temp.path(), &["runtime.c", "runtime.h"]).unwrap();
    let changed_names = runtime_inputs_fingerprint(temp.path(), &["runtime.h", "runtime.c"]).unwrap();

    assert_ne!(initial, changed_content);
    assert_ne!(changed_content, changed_names);
}

#[test]
fn test_core_c_runtime_target_flags_cover_aarch64_atomics_and_riscv_vectors() {
    use simple_common::target::{Target, TargetArch, TargetOS};

    assert_eq!(
        core_c_target_flags(
            Target::new(TargetArch::Aarch64, TargetOS::Linux),
            "runtime_native.c",
            false
        ),
        ["-mno-outline-atomics"]
    );
    assert_eq!(
        core_c_target_flags(
            Target::new(TargetArch::Riscv64, TargetOS::Linux),
            "runtime_simd_dispatch.c",
            true
        ),
        ["-march=rv64gcv", "-mabi=lp64d"]
    );
    assert!(core_c_target_flags(
        Target::new(TargetArch::Riscv64, TargetOS::Linux),
        "runtime_native.c",
        true
    )
    .is_empty());
}

#[cfg(target_os = "linux")]
fn run_required_abi_probe(repo_root: &Path, temp_root: &Path, runtime: &Path, label: &str) {
    let source = temp_root.join(format!("{label}_abi_probe.c"));
    let exe = temp_root.join(format!("{label}_abi_probe"));

    std::fs::write(
        &source,
        r#"
#include <stdint.h>
#include "runtime.h"

int main(void) {
    __simple_runtime_init();
    if (rt_value_as_int(rt_value_int(-7)) != -7) return 9;
    SplArray* values = rt_array_new(2);
    if (!values) return 10;
    if (!rt_array_push(values, rt_value_int(10))) return 11;
    if (!rt_array_push(values, rt_value_int(20))) return 12;
    if (rt_index_get((int64_t)values, rt_value_int(1)) != rt_value_int(20)) return 13;
    if (rt_index_get((int64_t)values, rt_value_int(-1)) != rt_value_int(20)) return 14;
    if (!rt_index_set((int64_t)values, rt_value_int(-1), rt_value_int(21))) return 15;
    if (rt_index_get((int64_t)values, rt_value_int(1)) != rt_value_int(21)) return 16;
    if (rt_index_get((int64_t)values, rt_value_int(-3)) != rt_value_nil()) return 17;
    if (rt_index_set((int64_t)values, rt_value_int(2), rt_value_int(99))) return 18;
    if (rt_index_get((int64_t)values, rt_value_nil()) != rt_value_nil()) return 19;
    SplArray* tail = rt_array_new(1);
    if (!tail || !rt_array_push(tail, rt_value_int(30))) return 20;
    SplArray* joined = rt_array_concat(values, tail);
    if (!joined || rt_array_len(joined) != 3) return 21;
    if (rt_array_get(joined, 0) != rt_value_int(10)) return 22;
    if (rt_array_get(joined, 1) != rt_value_int(21)) return 23;
    if (rt_array_get(joined, 2) != rt_value_int(30)) return 24;
    if (rt_array_len(values) != 2 || rt_array_len(tail) != 1) return 25;
    SplArray* byte_left = rt_byte_array_new(2);
    SplArray* byte_right = rt_byte_array_new(1);
    if (!byte_left || !byte_right) return 26;
    if (!rt_array_push(byte_left, rt_value_int('a')) || !rt_array_push(byte_left, rt_value_int('b'))) return 27;
    if (!rt_array_push(byte_right, rt_value_int('c'))) return 28;
    SplArray* byte_joined = rt_array_concat(byte_left, byte_right);
    if (!byte_joined || rt_array_len(byte_joined) != 3) return 29;
    if (rt_bytes_u8_at(byte_joined, 0) != 'a' || rt_bytes_u8_at(byte_joined, 2) != 'c') return 30;
    if (rt_array_concat(NULL, byte_right) != NULL) return 31;
    if (!rt_array_clear(joined) || rt_array_len(joined) != 0) return 32;
    if (rt_array_clear(NULL)) return 33;
    SplArray* mixed = rt_array_concat(tail, byte_left);
    if (!mixed || rt_array_len(mixed) != 3) return 34;
    if (rt_array_get(mixed, 0) != rt_value_int(30) || rt_array_get(mixed, 1) != rt_value_int('a')) return 35;
    SplArray* words_left = rt_array_new_with_cap_u64(1);
    SplArray* words_right = rt_array_new_with_cap_u64(1);
    if (!words_left || !words_right) return 36;
    if (!rt_typed_words_u64_push(words_left, 0x100000000LL)) return 37;
    if (!rt_typed_words_u64_push(words_right, -1LL)) return 38;
    SplArray* words_joined = rt_array_concat(words_left, words_right);
    if (!words_joined || rt_array_len(words_joined) != 2) return 39;
    if (rt_typed_words_u64_at(words_joined, 0) != 0x100000000LL ||
        rt_typed_words_u64_at(words_joined, 1) != -1LL) return 40;
    if (rt_array_concat(words_left, tail) != NULL) return 41;
    if (rt_array_new(100000001LL) != NULL) return 42;
    int64_t abc = rt_string_new((const uint8_t*)"abc", 3);
    SplArray* bytes = (SplArray*)(uintptr_t)rt_string_bytes(abc);
    if (rt_array_len(bytes) != 3) return 43;
    if (rt_array_get(bytes, 1) != rt_value_int('b')) return 44;
    int64_t utf8_chars_text = rt_string_new((const uint8_t*)"a\xC3\xA9", 3);
    SplArray* chars = (SplArray*)(uintptr_t)rt_string_chars(utf8_chars_text);
    if (rt_array_len(chars) != 2) return 45;
    int64_t second_char = rt_array_get(chars, 1);
    if (rt_string_len(second_char) != 2 || memcmp(rt_string_data(second_char), "\xC3\xA9", 2) != 0) return 46;
    int64_t keyword_text = rt_string_new((const uint8_t*)"fn", 2);
    SplArray* keyword_chars = (SplArray*)(uintptr_t)rt_string_chars(keyword_text);
    int64_t keyword_slice = rt_slice((int64_t)(uintptr_t)keyword_chars, 0, 2, 1);
    int64_t keyword_join = rt_string_join(keyword_slice, rt_string_new(NULL, 0));
    if (rt_string_len(keyword_join) != 2 || memcmp(rt_string_data(keyword_join), "fn", 2) != 0) return 47;
    if (!rt_is_none(rt_value_nil()) || rt_is_none(rt_value_int(1))) return 48;
    if (rt_is_none(0) || !rt_is_some(0) || !rt_is_some(rt_value_int(1))) return 49;
    int64_t byte_stride = rt_slice((int64_t)(uintptr_t)byte_left, 0, 2, 2);
    if (rt_array_len((SplArray*)(uintptr_t)byte_stride) != 1 ||
        rt_bytes_u8_at((SplArray*)(uintptr_t)byte_stride, 0) != 'a') return 50;
    int64_t empty_bytes = rt_slice((int64_t)(uintptr_t)byte_left, 0, 0, 1);
    if (!rt_typed_bytes_u8_push((SplArray*)(uintptr_t)empty_bytes, 'z') ||
        rt_bytes_u8_at((SplArray*)(uintptr_t)empty_bytes, 0) != 'z') return 51;
    int64_t empty_words = rt_slice((int64_t)(uintptr_t)words_joined, 0, 0, 1);
    if (!rt_typed_words_u64_push((SplArray*)(uintptr_t)empty_words, 0x100000001LL) ||
        rt_typed_words_u64_at((SplArray*)(uintptr_t)empty_words, 0) != 0x100000001LL) return 52;
    int64_t joined_path = rt_path_join((const uint8_t*)"/tmp/cache", 10, (const uint8_t*)"object", 6);
    if (rt_string_len(joined_path) != 17 ||
        memcmp(rt_string_data(joined_path), "/tmp/cache/object", 17) != 0) return 53;
    int64_t absolute_path = rt_path_join((const uint8_t*)"/tmp/cache", 10, (const uint8_t*)"/etc/config", 11);
    if (rt_string_len(absolute_path) != 11 ||
        memcmp(rt_string_data(absolute_path), "/etc/config", 11) != 0) return 54;
    int64_t empty_right_path = rt_path_join((const uint8_t*)"/tmp/cache/", 11, NULL, 0);
    if (rt_string_len(empty_right_path) != 11 ||
        memcmp(rt_string_data(empty_right_path), "/tmp/cache/", 11) != 0) return 55;
    int64_t empty_left_path = rt_path_join((const uint8_t*)"", 0, (const uint8_t*)"object", 6);
    if (rt_string_len(empty_left_path) != 6 ||
        memcmp(rt_string_data(empty_left_path), "object", 6) != 0) return 56;
    int64_t single_separator_path = rt_path_join((const uint8_t*)"/tmp/cache/", 11, (const uint8_t*)"object", 6);
    if (rt_string_len(single_separator_path) != 17 ||
        memcmp(rt_string_data(single_separator_path), "/tmp/cache/object", 17) != 0) return 57;
    if (rt_string_new((const uint8_t*)"x", UINT64_MAX) != rt_value_nil()) return 58;
    int64_t out = rt_string_new((const uint8_t*)"out:", 4);
    int64_t err = rt_string_new((const uint8_t*)"err", 3);
    rt_stdout_write(out);
    print_raw(stdin_read_char());
    rt_print_value(rt_value_int(7));
    rt_print_value(rt_value_bool(1));
    rt_print_value(rt_value_nil());
    rt_stdout_flush();
    rt_stderr_write(err);
    rt_stderr_flush();
    __simple_runtime_shutdown();
    return 0;
}
"#,
    )
    .unwrap();

    let status = std::process::Command::new(find_c_compiler())
        .arg("-I")
        .arg(repo_root.join("src/runtime"))
        .arg(&source)
        .arg(runtime)
        .args(["-lpthread", "-ldl", "-lm"])
        .arg("-o")
        .arg(&exe)
        .status()
        .unwrap();
    assert!(status.success(), "failed to compile {label} ABI probe");

    let mut child = std::process::Command::new(&exe)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    {
        use std::io::Write;
        child.stdin.as_mut().unwrap().write_all(b"Z").unwrap();
    }
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{label} ABI probe exited unsuccessfully: status={} stdout={:?} stderr={:?}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "out:Z7true");
    assert_eq!(String::from_utf8_lossy(&output.stderr), "err");
}

#[cfg(target_os = "linux")]
#[test]
fn test_core_lane_runtime_required_abi_stdout_stderr_and_values() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let temp = tempfile::tempdir().unwrap();
    let core_c =
        build_core_c_runtime_library(&temp.path().join("core_c")).expect("core-c runtime archive should build");

    run_required_abi_probe(&repo_root, temp.path(), &core_c, "core_c");

    if let Some(simple_core) = find_abi_complete_simple_core_runtime_library() {
        run_required_abi_probe(&repo_root, temp.path(), &simple_core, "simple_core");
    }
}

#[test]
fn test_find_native_all_library_does_not_search_compiler_rust_target() {
    let temp = tempfile::tempdir().unwrap();
    let debug_dir = temp.path().join("src/compiler_rust/target/debug");
    let release_dir = temp.path().join("src/compiler_rust/target/release");
    std::fs::create_dir_all(&debug_dir).unwrap();
    std::fs::create_dir_all(&release_dir).unwrap();

    let empty_debug = debug_dir.join("libsimple_native_all.a");
    let release = release_dir.join("libsimple_native_all.a");
    std::fs::write(&empty_debug, b"").unwrap();
    std::fs::write(&release, b"real archive").unwrap();

    let selected = with_current_dir(temp.path(), find_native_all_library);
    assert!(selected.is_none());
}

#[cfg(target_os = "linux")]
#[test]
fn test_requested_symbol_owners_reject_empty_request() {
    let error = super::tools::validate_requested_symbol_owners(&[], &[]).unwrap_err();

    assert_eq!(error, "Stage4 requested symbol set is empty");
}

#[cfg(target_os = "linux")]
#[test]
fn test_requested_symbol_owners_are_stable_sorted_and_unique() {
    let temp = tempfile::tempdir().unwrap();
    let later = build_compiler_backfill_test_archive(temp.path(), "later", &["void requested_z(void) {}\n"]);
    let earlier = build_compiler_backfill_test_archive(temp.path(), "earlier", &["void requested_a(void) {}\n"]);

    let owners = super::tools::validate_requested_symbol_owners(
        &[("later", &later), ("earlier", &earlier)],
        &["requested_z", "requested_a", "requested_z"],
    )
    .unwrap();

    assert_eq!(
        owners.into_iter().collect::<Vec<_>>(),
        vec![
            ("requested_a".to_string(), "earlier".to_string()),
            ("requested_z".to_string(), "later".to_string()),
        ]
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_requested_symbol_owners_reject_missing_symbols_in_stable_order() {
    let temp = tempfile::tempdir().unwrap();
    let archive = build_compiler_backfill_test_archive(temp.path(), "owned", &["void requested_owned(void) {}\n"]);

    let error = super::tools::validate_requested_symbol_owners(
        &[("owned", &archive)],
        &["requested_missing_z", "requested_missing_a"],
    )
    .unwrap_err();

    assert_eq!(
        error,
        "Stage4 requested symbols have no archive owner: requested_missing_a, requested_missing_z"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_requested_symbol_owners_reject_duplicate_owners() {
    let temp = tempfile::tempdir().unwrap();
    let first = build_compiler_backfill_test_archive(temp.path(), "first_owner", &["void requested_shared(void) {}\n"]);
    let second =
        build_compiler_backfill_test_archive(temp.path(), "second_owner", &["void requested_shared(void) {}\n"]);

    let error = super::tools::validate_requested_symbol_owners(
        &[("first", &first), ("second", &second)],
        &["requested_shared"],
    )
    .unwrap_err();

    assert_eq!(
        error,
        "Stage4 archive overlap: `requested_shared` is defined by both first and second"
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_keeps_exact_manifest_and_localizes_dependency_closure() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "compiler",
        &[r#"
void hidden_helper(void) {}
void rt_cranelift_requested_hook(void) { hidden_helper(); }
__attribute__((constructor)) static void compiler_ctor(void) { hidden_helper(); }
"#],
    );
    let provider = build_compiler_backfill_test_archive(temp.path(), "provider", &["void provider_only(void) {}\n"]);
    let output_dir = temp.path().join("output");

    let output = build_compiler_backfill_archive(&compiler, &[provider], &output_dir).unwrap();
    assert_eq!(output, output_dir.join("libsimple_compiler_backfill.a"));
    let (defined, undefined) = super::tools::archive_global_symbols(&output).unwrap();
    assert_eq!(defined.get("rt_cranelift_requested_hook"), Some(&1));
    assert!(!defined.contains_key("hidden_helper"));
    assert_eq!(defined.len(), 1);
    assert!(!undefined
        .iter()
        .any(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_")));
    assert_eq!(archive_members(&output).unwrap(), ["compiler_backfill_local.o"]);
    let symbols = nm_command().arg("--defined-only").arg(&output).output().unwrap();
    assert!(symbols.status.success());
    let symbols = String::from_utf8_lossy(&symbols.stdout);
    assert!(symbols.lines().any(|line| {
        let fields: Vec<&str> = line.split_whitespace().collect();
        matches!(fields.as_slice(), [_address, "t", "hidden_helper"])
    }));
    assert!(!symbols.contains("__simple_compiler_backfill_private_"));
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_rejects_missing_derived_contract() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(temp.path(), "compiler", &["void requested_hook(void) {}\n"]);
    let output_dir = temp.path().join("output");

    let error = build_compiler_backfill_archive(&compiler, &[], &output_dir).unwrap_err();
    assert!(error.contains("defines no rt_cranelift_* exports"));
    assert!(!output_dir.join("libsimple_compiler_backfill.a").exists());
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_requires_each_export_exactly_once() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "compiler",
        &[
            "void rt_cranelift_requested_hook(void) {}\n",
            "void rt_cranelift_requested_hook(void) {}\n",
        ],
    );

    let error = build_compiler_backfill_archive(&compiler, &[], &temp.path().join("output")).unwrap_err();
    assert!(error.contains("must be defined exactly once"));
    assert!(error.contains("found 2"));
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_rejects_runtime_provider_dependencies() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "compiler",
        &["extern void rt_missing(void); void rt_cranelift_requested_hook(void) { rt_missing(); }\n"],
    );

    let error = build_compiler_backfill_archive(&compiler, &[], &temp.path().join("output")).unwrap_err();
    assert!(error.contains("runtime/provider ownership outside the manifest"));
    assert!(error.contains("rt_missing"));
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_rejects_same_archive_runtime_laundering() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "compiler",
        &[
            "extern void rt_hidden_runtime(void); void rt_cranelift_requested_hook(void) { rt_hidden_runtime(); }\n",
            "void rt_hidden_runtime(void) {}\n",
        ],
    );
    let output_dir = temp.path().join("output");

    let error = build_compiler_backfill_archive(&compiler, &[], &output_dir).unwrap_err();
    assert!(error.contains("runtime/provider ownership outside the manifest"));
    assert!(error.contains("rt_hidden_runtime"));
    assert!(!output_dir.join("libsimple_compiler_backfill.a").exists());
}

#[cfg(target_os = "linux")]
#[test]
fn test_compiler_backfill_archive_rejects_provider_symbol_overlap() {
    let temp = tempfile::tempdir().unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "compiler",
        &["void rt_cranelift_requested_hook(void) {}\n"],
    );
    let provider = build_compiler_backfill_test_archive(
        temp.path(),
        "provider",
        &["void rt_cranelift_requested_hook(void) {}\n"],
    );

    let error =
        build_compiler_backfill_archive(&compiler, std::slice::from_ref(&provider), &temp.path().join("output"))
            .unwrap_err();
    assert!(error.contains(&provider.display().to_string()));
    assert!(error.contains("rt_cranelift_requested_hook"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_provider_archives_have_exact_members_and_contracts() {
    let temp = tempfile::tempdir().unwrap();
    let archives = build_stage4_cli_c_provider_archives(temp.path()).unwrap();
    let expected = [
        ("libsimple_stage4_time.a", "runtime_timestamp.o", "runtime_timestamp.c"),
        ("libsimple_stage4_sqlite.a", "runtime_sqlite.o", "runtime_sqlite.c"),
    ];
    assert_eq!(archives.len(), expected.len());
    for (archive, (archive_name, member_name, source_name)) in archives.iter().zip(expected) {
        assert_eq!(archive.file_name().and_then(|name| name.to_str()), Some(archive_name));
        assert_eq!(archive_members(archive).unwrap(), [member_name]);
        super::tools::validate_stage4_cli_c_provider_archive_contract(archive, source_name).unwrap();
    }
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_providers_are_disjoint_from_current_core_c() {
    let temp = tempfile::tempdir().unwrap();
    let core = build_core_c_runtime_library(&temp.path().join("core")).unwrap();
    let compiler = build_compiler_backfill_test_archive(
        temp.path(),
        "stage4_clean_compiler",
        &["void rt_cranelift_requested_hook(void) {}\n"],
    );
    let providers = build_stage4_cli_c_provider_archives(&temp.path().join("providers")).unwrap();

    validate_stage4_cli_c_provider_archive_disjointness(&core, &compiler, &providers).unwrap();
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
fn run_stage4_c_probe(
    root: &Path,
    name: &str,
    source_text: &str,
    archives: &[&Path],
    link_args: &[&str],
    run_args: &[&Path],
) {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let source = root.join(format!("{name}.c"));
    let executable = root.join(name);
    std::fs::write(&source, source_text).unwrap();
    let mut command = std::process::Command::new(find_c_compiler());
    command.arg("-I").arg(repo_root.join("src/runtime")).arg(&source);
    for archive in archives {
        command.arg(archive);
    }
    let compile = command.args(link_args).arg("-o").arg(&executable).output().unwrap();
    assert!(
        compile.status.success(),
        "failed to compile {name}: {}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let output = std::process::Command::new(&executable).args(run_args).output().unwrap();
    assert!(
        output.status.success(),
        "{name} failed: status={} stdout={:?} stderr={:?}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_enum_id_hosted_c_runtime_behavior() {
    let temp = tempfile::tempdir().unwrap();
    let core = build_core_c_runtime_library(&temp.path().join("core")).unwrap();
    run_stage4_c_probe(
        temp.path(),
        "hosted_enum_id_probe",
        r#"
#include <stdint.h>
#include "runtime.h"

int main(void) {
    int64_t value = rt_enum_new(7, 2, 11);
    if (rt_enum_id(value) != 7) return 1;
    if (rt_enum_id(0) != -1) return 2;
    return 0;
}
"#,
        &[core.as_path()],
        &["-lpthread", "-ldl", "-lm"],
        &[],
    );
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_enum_id_weak_c_runtime_behavior() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let runtime_root = repo_root.join("src/runtime");
    let temp = tempfile::tempdir().unwrap();
    let probe = temp.path().join("weak_enum_id_probe.c");
    let probe_object = temp.path().join("weak_enum_id_probe.o");
    let runtime_object = temp.path().join("runtime.o");
    let memtrack_object = temp.path().join("runtime_memtrack.o");
    let executable = temp.path().join("weak_enum_id_probe");
    let runtime_source = runtime_root.join("runtime.c");
    let memtrack_source = runtime_root.join("runtime_memtrack.c");
    std::fs::write(
        &probe,
        r#"
#include <stdint.h>
#include "runtime.h"

int main(void) {
    int64_t value = rt_enum_new(9, 3, 17);
    if (rt_enum_id(value) != 9) return 1;
    if (rt_enum_id(0) != -1) return 2;
    return 0;
}
"#,
    )
    .unwrap();
    let cc = find_c_compiler();
    for (source, object) in [
        (probe.as_path(), probe_object.as_path()),
        (runtime_source.as_path(), runtime_object.as_path()),
        (memtrack_source.as_path(), memtrack_object.as_path()),
    ] {
        let output = std::process::Command::new(&cc)
            .args(["-c", "-ffunction-sections", "-fdata-sections"])
            .arg("-I")
            .arg(&runtime_root)
            .arg(source)
            .arg("-o")
            .arg(object)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "failed to compile {}: {}",
            source.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let output = std::process::Command::new(&cc)
        .args(["-Wl,--gc-sections"])
        .arg(&probe_object)
        .arg(&runtime_object)
        .arg(&memtrack_object)
        .args(["-lpthread", "-ldl", "-lm"])
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "failed to link weak enum probe: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(std::process::Command::new(&executable).status().unwrap().success());
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_core_c_memtrack_provider_real_behavior() {
    let temp = tempfile::tempdir().unwrap();
    let core = build_core_c_runtime_library(&temp.path().join("core")).unwrap();
    let dump = temp.path().join("memtrack.dump");
    run_stage4_c_probe(
        temp.path(),
        "stage4_memtrack_probe",
        r#"
#include <stdint.h>
#include "runtime_memtrack.h"

int main(int argc, char **argv) {
    int first = 1;
    int second = 2;
    if (argc != 2) return 1;
    spl_memtrack_reset();
    spl_memtrack_enable();
    if (!spl_memtrack_is_enabled()) return 2;
    int64_t snapshot = spl_memtrack_snapshot();
    spl_memtrack_record(&first, 12, "first");
    spl_memtrack_record(&second, 20, "second");
    if (spl_memtrack_count_since(snapshot) != 2) return 3;
    if (spl_memtrack_bytes_since(snapshot) != 32) return 4;
    if (spl_memtrack_live_count() != 2 || spl_memtrack_live_bytes() != 32) return 5;
    spl_memtrack_unrecord(&first);
    if (spl_memtrack_count_since(snapshot) != 1) return 6;
    if (spl_memtrack_bytes_since(snapshot) != 20) return 7;
    if (spl_memtrack_live_count() != 1 || spl_memtrack_live_bytes() != 20) return 8;
    spl_memtrack_dump_since(snapshot, argv[1]);
    spl_memtrack_reset();
    if (spl_memtrack_snapshot() != 0) return 9;
    if (spl_memtrack_live_count() != 0 || spl_memtrack_live_bytes() != 0) return 10;
    spl_memtrack_disable();
    return 0;
}
"#,
        &[core.as_path()],
        &[],
        &[dump.as_path()],
    );
    let dump_text = std::fs::read_to_string(dump).unwrap();
    assert!(dump_text.contains("20 second"));
    assert!(!dump_text.contains("first"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_sqlite_provider_round_trips_core_strings() {
    let temp = tempfile::tempdir().unwrap();
    let providers = build_stage4_cli_c_provider_archives(&temp.path().join("providers")).unwrap();
    let core = build_core_c_runtime_library(&temp.path().join("core")).unwrap();
    run_stage4_c_probe(
        temp.path(),
        "stage4_sqlite_probe",
        r#"
#include <stdint.h>
#include <string.h>
#include "runtime.h"

extern int64_t rt_sqlite_open_memory(void);
extern int64_t rt_sqlite_close(int64_t handle);
extern int64_t rt_sqlite_execute(int64_t connection, int64_t sql);
extern int64_t rt_sqlite_query(int64_t connection, int64_t sql);
extern int64_t rt_sqlite_query_next(int64_t statement);
extern void rt_sqlite_query_done(int64_t statement);
extern int64_t rt_sqlite_column_name(int64_t statement, int64_t index);
extern int64_t rt_sqlite_column_text(int64_t statement, int64_t index);
extern int64_t rt_sqlite_error_message(int64_t connection);

static int64_t text(const char *value) {
    return rt_string_new((const uint8_t *)value, strlen(value));
}

static int text_equals(int64_t value, const char *expected) {
    uint64_t len = strlen(expected);
    return rt_string_len(value) == (int64_t)len && memcmp(rt_string_data(value), expected, len) == 0;
}

static int text_contains(int64_t value, const char *needle) {
    uint64_t len = (uint64_t)rt_string_len(value);
    uint64_t needle_len = strlen(needle);
    const uint8_t *data = rt_string_data(value);
    if (!data || needle_len > len) return 0;
    for (uint64_t i = 0; i + needle_len <= len; i++) {
        if (memcmp(data + i, needle, needle_len) == 0) return 1;
    }
    return 0;
}

int main(void) {
    __simple_runtime_init();
    int64_t connection = rt_sqlite_open_memory();
    if (connection == rt_value_nil()) return 1;
    if (rt_sqlite_execute(connection, text("CREATE TABLE item(label TEXT)")) != rt_value_int(1)) return 2;
    if (rt_sqlite_execute(connection, text("INSERT INTO item VALUES ('hello')")) != rt_value_int(1)) return 3;
    int64_t statement = rt_sqlite_query(connection, text("SELECT label AS item_name FROM item"));
    if (statement == rt_value_nil()) return 4;
    if (rt_sqlite_query_next(statement) != rt_value_int(1)) return 5;
    int64_t index = rt_value_int(0);
    if (!text_equals(rt_sqlite_column_name(statement, index), "item_name")) return 6;
    if (!text_equals(rt_sqlite_column_text(statement, index), "hello")) return 7;
    if (rt_sqlite_query_next(statement) != rt_value_int(0)) return 8;
    rt_sqlite_query_done(statement);
    if (rt_sqlite_execute(connection, text("invalid sql")) != rt_value_int(0)) return 9;
    if (!text_contains(rt_sqlite_error_message(connection), "syntax")) return 10;
    if (rt_sqlite_close(connection) != rt_value_int(1)) return 11;
    __simple_runtime_shutdown();
    return 0;
}
"#,
        &[providers[1].as_path(), core.as_path()],
        &["-lsqlite3", "-lpthread", "-ldl", "-lm"],
        &[],
    );
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_provider_contract_rejects_unexpected_global_and_undefined() {
    let temp = tempfile::tempdir().unwrap();
    let archive = build_compiler_backfill_test_archive(
        temp.path(),
        "bad_sqlite_provider",
        &["extern void surprise(void); long rt_sqlite_open(long value) { surprise(); return value; } void unexpected_global(void) {}\n"],
    );

    let error =
        super::tools::validate_stage4_cli_c_provider_archive_contract(&archive, "runtime_sqlite.c").unwrap_err();
    assert!(error.contains("unexpected_global"));
    assert!(error.contains("missing undefined ["));
    assert!(error.contains("unexpected undefined [surprise]"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_provider_contract_rejects_constructor_and_duplicate_definition() {
    let temp = tempfile::tempdir().unwrap();
    let constructor = build_compiler_backfill_test_archive(
        temp.path(),
        "constructor_provider",
        &["__attribute__((constructor)) static void start(void) {} void rt_time_now_seconds_f64(void) {}\n"],
    );
    let error =
        super::tools::validate_stage4_cli_c_provider_archive_contract(&constructor, "runtime_timestamp.c").unwrap_err();
    assert!(error.contains("constructor/destructor sections"));

    let duplicate = build_compiler_backfill_test_archive(
        temp.path(),
        "duplicate_provider",
        &[
            "void rt_time_now_seconds_f64(void) {}\n",
            "void rt_time_now_seconds_f64(void) {}\n",
        ],
    );
    let error =
        super::tools::validate_stage4_cli_c_provider_archive_contract(&duplicate, "runtime_timestamp.c").unwrap_err();
    assert!(error.contains("rt_time_now_seconds_f64 (2)"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_provider_disjointness_rejects_overlap() {
    let temp = tempfile::tempdir().unwrap();
    let core = build_compiler_backfill_test_archive(
        temp.path(),
        "stage4_core",
        &[r#"
long rt_string_new(void) { return 0; }
long rt_string_data(void) { return 0; }
double rt_time_now_seconds_f64(void) { return 0.0; }
"#],
    );
    let compiler =
        build_compiler_backfill_test_archive(temp.path(), "stage4_compiler", &["void compiler_only(void) {}\n"]);
    let providers = build_stage4_cli_c_provider_archives(&temp.path().join("providers")).unwrap();

    let error = validate_stage4_cli_c_provider_archive_disjointness(&core, &compiler, &providers).unwrap_err();
    assert!(error.contains("`rt_time_now_seconds_f64`"));
    assert!(error.contains("both core and runtime_timestamp.c"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_cli_c_provider_disjointness_requires_exact_component_set() {
    let missing = Path::new("missing");
    let error = validate_stage4_cli_c_provider_archive_disjointness(missing, missing, &[]).unwrap_err();
    assert!(error.contains("requires exactly 2 providers (found 0)"));
}

#[test]
fn test_stage4_rust_runtime_selector_requires_staticlib() {
    let temp = tempfile::tempdir().unwrap();
    let deps = temp.path().join("deps");
    std::fs::create_dir_all(&deps).unwrap();
    let staticlib = deps.join("libsimple_runtime.a");
    std::fs::write(&staticlib, b"staticlib").unwrap();
    std::fs::write(deps.join("libsimple_runtime.rlib"), b"rlib").unwrap();

    assert_eq!(
        NativeProjectBuilder::stage4_rust_runtime_staticlib(temp.path()).unwrap(),
        staticlib
    );
    std::fs::remove_file(&staticlib).unwrap();
    let error = NativeProjectBuilder::stage4_rust_runtime_staticlib(temp.path()).unwrap_err();
    assert!(error.contains(&staticlib.display().to_string()));
    assert!(error.contains("staticlib"));
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_runtime_capsule_keeps_only_requested_globals() {
    let temp = tempfile::tempdir().unwrap();
    let core = build_compiler_backfill_test_archive(
        temp.path(),
        "stage4_runtime_core",
        &[r#"
static void retained_helper(void) {}
void rt_capsule_root(void) { retained_helper(); }
__attribute__((constructor)) static void discarded_ctor(void) { retained_helper(); }
"#],
    );
    let providers = build_stage4_cli_c_provider_archives(&temp.path().join("providers")).unwrap();
    let output = build_stage4_runtime_capsule_archive(
        &core,
        &providers,
        &["rt_time_now_seconds_f64".to_string(), "rt_capsule_root".to_string()],
        &temp.path().join("capsule"),
    )
    .unwrap();

    let (defined, undefined) = super::tools::archive_global_symbols(&output).unwrap();
    assert_eq!(
        defined,
        std::collections::BTreeMap::from([
            ("rt_capsule_root".to_string(), 1),
            ("rt_time_now_seconds_f64".to_string(), 1),
        ])
    );
    assert!(!undefined
        .iter()
        .any(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_")));
    assert_eq!(archive_members(&output).unwrap(), ["stage4_runtime_capsule_local.o"]);
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_linux_exact_core_projects_fail_closed_platform_abi() {
    const REQUESTED: &[&str] = &[
        "rt_cocoa_layer_blend_rect",
        "rt_cocoa_layer_blur",
        "rt_cocoa_layer_create",
        "rt_cocoa_layer_gradient_v",
        "rt_cocoa_layer_read_pixel",
        "rt_cocoa_window_close",
        "rt_cocoa_window_new",
        "rt_win32_dib_create",
        "rt_win32_dib_fill_rect",
        "rt_win32_dib_present",
        "rt_win32_dib_present_rect",
        "rt_win32_window_close",
        "rt_win32_window_new",
    ];

    let temp = tempfile::tempdir().unwrap();
    let core = build_core_c_runtime_library(&temp.path().join("core")).unwrap();
    let providers = build_stage4_cli_c_provider_archives(&temp.path().join("providers")).unwrap();
    let requested: Vec<String> = REQUESTED.iter().map(|symbol| (*symbol).to_string()).collect();
    let capsule =
        build_stage4_runtime_capsule_archive(&core, &providers, &requested, &temp.path().join("capsule")).unwrap();

    let (defined, undefined) = super::tools::archive_global_symbols(&capsule).unwrap();
    assert_eq!(
        defined,
        REQUESTED
            .iter()
            .map(|symbol| ((*symbol).to_string(), 1))
            .collect::<std::collections::BTreeMap<_, _>>()
    );
    assert!(!undefined
        .iter()
        .any(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_")));

    run_stage4_c_probe(
        temp.path(),
        "stage4_fail_closed_platform_probe",
        r#"
#include <stdbool.h>
#include <stdint.h>

extern int64_t rt_cocoa_window_new(int64_t, int64_t, int64_t);
extern bool rt_cocoa_window_close(int64_t);
extern int64_t rt_cocoa_layer_create(int64_t, int64_t, int64_t, int64_t);
extern bool rt_cocoa_layer_blend_rect(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
extern int64_t rt_win32_window_new(int64_t, int64_t, int64_t);
extern bool rt_win32_window_close(int64_t);
extern int64_t rt_win32_dib_create(int64_t, int64_t, int64_t, int64_t);
extern bool rt_win32_dib_fill_rect(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);

int main(void) {
    if (rt_cocoa_window_new(1, 1, 0) != -1 || rt_cocoa_window_close(1)) return 1;
    if (rt_cocoa_layer_create(1, 1, 1, 0) != -1 || rt_cocoa_layer_blend_rect(1, 0, 0, 1, 1, 0, 0)) return 2;
    if (rt_win32_window_new(1, 1, 0) != -1 || rt_win32_window_close(1)) return 3;
    if (rt_win32_dib_create(1, 1, 1, 0) != -1 || rt_win32_dib_fill_rect(1, 0, 0, 1, 1, 0)) return 4;
    return 0;
}
"#,
        &[&capsule],
        &[],
        &[],
    );
}

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[test]
fn test_stage4_rust_runtime_projection_keeps_roots_and_allowed_runtime_externals_only() {
    let temp = tempfile::tempdir().unwrap();
    let rust_runtime = build_compiler_backfill_test_archive(
        temp.path(),
        "stage4_rust_runtime_source",
        &[r#"
extern void rt_adjacent_capsule(void);
static void retained_helper(void) { rt_adjacent_capsule(); }
void rt_projected_root(void) { retained_helper(); }
void rt_unrequested_export(void) {}
__attribute__((constructor)) static void discarded_ctor(void) { rt_unrequested_export(); }
"#],
    );
    let output = build_stage4_rust_runtime_projection_archive(
        &rust_runtime,
        &["rt_projected_root".to_string()],
        &["rt_adjacent_capsule".to_string()],
        &temp.path().join("projection"),
    )
    .unwrap();

    let (defined, undefined) = super::tools::archive_global_symbols(&output).unwrap();
    assert_eq!(
        defined,
        std::collections::BTreeMap::from([("rt_projected_root".to_string(), 1)])
    );
    assert_eq!(
        undefined
            .iter()
            .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
            .cloned()
            .collect::<Vec<_>>(),
        ["rt_adjacent_capsule"]
    );
    assert_eq!(archive_members(&output).unwrap(), ["stage4_rust_runtime_local.o"]);
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn test_stage4_compiler_entry_authorization_requires_both_envs_and_exact_entry() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    let temp = tempfile::tempdir().unwrap();
    let entry = temp.path().join("src/app/cli/native_build_main.spl");
    std::fs::create_dir_all(entry.parent().unwrap()).unwrap();
    std::fs::write(&entry, "fn main() -> i64: 0\n").unwrap();
    let builder = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("out")).entry_file(entry);

    unsafe {
        std::env::remove_var("SIMPLE_BOOTSTRAP");
        std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4");
    }
    assert!(!builder.is_authorized_stage4_compiler_entry());
    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", "1") };
    assert!(!builder.is_authorized_stage4_compiler_entry());
    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1") };
    assert!(builder.is_authorized_stage4_compiler_entry());

    let cli_entry = temp.path().join("src/app/cli/main.spl");
    std::fs::write(&cli_entry, "fn main() -> i64: 0\n").unwrap();
    let cli_builder =
        NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("cli-out")).entry_file(cli_entry);
    assert!(cli_builder.is_authorized_stage4_compiler_entry());

    let no_entry = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("no-entry-out"));
    assert!(!no_entry.is_authorized_stage4_compiler_entry());
    let bootstrap_entry = temp.path().join("src/app/cli/bootstrap_main.spl");
    std::fs::write(&bootstrap_entry, "fn main() -> i64: 0\n").unwrap();
    let bootstrap = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("bootstrap-out"))
        .entry_file(bootstrap_entry);
    assert!(!bootstrap.is_authorized_stage4_compiler_entry());

    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "true") };
    assert!(!builder.is_authorized_stage4_compiler_entry());
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
        std::env::set_var("SIMPLE_BOOTSTRAP", "true");
    }
    assert!(!builder.is_authorized_stage4_compiler_entry());
    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", "1") };

    let spoof = temp.path().join("other/src/app/cli/main.spl");
    std::fs::create_dir_all(spoof.parent().unwrap()).unwrap();
    std::fs::write(&spoof, "fn main() -> i64: 0\n").unwrap();
    let spoof_builder =
        NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("spoof-out")).entry_file(spoof);
    assert!(!spoof_builder.is_authorized_stage4_compiler_entry());

    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
#[test]
fn test_stage4_compiler_entry_is_disabled_without_supported_capsule_linker() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP", "1");
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
    }
    let temp = tempfile::tempdir().unwrap();
    let entry = temp.path().join("src/app/cli/main.spl");
    std::fs::create_dir_all(entry.parent().unwrap()).unwrap();
    std::fs::write(&entry, "fn main() -> i64: 0\n").unwrap();
    let builder = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("out")).entry_file(entry);
    assert!(!builder.is_authorized_stage4_compiler_entry());

    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
}

#[cfg(target_os = "linux")]
#[test]
fn test_stage4_compiler_entries_select_only_dedicated_compiler_backfill() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP", "1");
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
    }

    let temp = tempfile::tempdir().unwrap();
    let runtime_path = temp.path().join("runtime");
    std::fs::create_dir_all(&runtime_path).unwrap();
    std::fs::write(runtime_path.join("libsimple_compiler.a"), b"full-compiler-decoy").unwrap();
    std::fs::write(runtime_path.join("libsimple_native_all.a"), b"native-all-decoy").unwrap();
    let config = NativeBuildConfig {
        runtime_path: Some(runtime_path.clone()),
        ..Default::default()
    };

    let focused_entry = temp.path().join("src/app/cli/native_build_main.spl");
    std::fs::create_dir_all(focused_entry.parent().unwrap()).unwrap();
    std::fs::write(&focused_entry, "fn main() -> i64: 0\n").unwrap();
    let focused = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("focused-out"))
        .config(config.clone())
        .entry_file(focused_entry.clone());

    let error = focused.selected_stage4_compiler_backfill_archive().unwrap_err();
    assert!(error.contains("libsimple_compiler_backfill.a"));

    let full_entry = temp.path().join("src/app/cli/main.spl");
    std::fs::write(&full_entry, "fn main() -> i64: 0\n").unwrap();
    let full = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("full-out"))
        .config(config)
        .entry_file(full_entry.clone());
    let error = full.selected_stage4_compiler_backfill_archive().unwrap_err();
    assert!(error.contains("libsimple_compiler_backfill.a"));

    let dedicated = runtime_path.join("libsimple_compiler_backfill.a");
    std::fs::write(&dedicated, b"dedicated-backfill").unwrap();
    assert_eq!(
        focused.selected_stage4_compiler_backfill_archive().unwrap(),
        Some(dedicated.clone())
    );
    assert_eq!(
        full.selected_stage4_compiler_backfill_archive().unwrap(),
        Some(dedicated)
    );
    let native_all = (runtime_path.join("libsimple_native_all.a"), true);
    assert!(focused.reject_unexpected_native_all(Some(&native_all)).is_err());
    assert!(full.reject_unexpected_native_all(Some(&native_all)).is_err());
    for entry in [focused_entry.clone(), full_entry.clone()] {
        let without_runtime =
            NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("missing-runtime-out"))
                .entry_file(entry);
        assert!(without_runtime
            .selected_stage4_compiler_backfill_archive()
            .unwrap_err()
            .contains("explicit runtime path"));
    }
    for entry in [focused_entry, full_entry] {
        for (bundle, expected) in [
            ("hosted", "removed Rust-hosted runtime bundles"),
            ("simple-core", "requires the core-c-bootstrap runtime lane"),
        ] {
            let mut rejected = NativeBuildConfig {
                runtime_path: Some(runtime_path.clone()),
                ..Default::default()
            };
            rejected.runtime_bundle = bundle.to_string();
            let builder = NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join("rejected-out"))
                .config(rejected)
                .entry_file(entry.clone());
            assert!(builder
                .selected_runtime_library(&temp.path().join("rejected-link"))
                .unwrap_err()
                .contains(expected));
        }
    }

    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
}

#[cfg(target_os = "linux")]
#[test]
fn test_core_c_runtime_native_focus_contract() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let temp = tempfile::tempdir().unwrap();
    let runtime = build_core_c_runtime_library(temp.path()).expect("core-c runtime archive should build");
    let executable = temp.path().join("runtime_native_focus_test");
    let status = std::process::Command::new(find_c_compiler())
        .arg("-I")
        .arg(repo_root.join("src/runtime"))
        .arg(repo_root.join("test/01_unit/runtime/runtime_native_focus_test.c"))
        .arg(&runtime)
        .args(["-lpthread", "-ldl", "-lm"])
        .arg("-o")
        .arg(&executable)
        .status()
        .unwrap();
    assert!(status.success(), "failed to compile runtime_native_focus_test.c");
    let output = std::process::Command::new(&executable).output().unwrap();
    assert!(
        output.status.success(),
        "runtime native focus contract failed: status={} stdout={:?} stderr={:?}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_stage4_compiler_entries_prepare_dedicated_backfill_through_gate() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP", "1");
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
    }

    let temp = tempfile::tempdir().unwrap();
    let runtime_path = temp.path().join("runtime");
    std::fs::create_dir_all(&runtime_path).unwrap();
    let dedicated = build_compiler_backfill_test_archive(
        &runtime_path,
        "simple_compiler_backfill",
        &["void hidden_helper(void) {}\nvoid rt_cranelift_requested_hook(void) { hidden_helper(); }\n"],
    );
    assert_eq!(dedicated, runtime_path.join("libsimple_compiler_backfill.a"));
    let provider = build_compiler_backfill_test_archive(temp.path(), "core_provider", &["void core_only(void) {}\n"]);
    let cli_dir = temp.path().join("src/app/cli");
    std::fs::create_dir_all(&cli_dir).unwrap();
    for entry_name in ["main.spl", "native_build_main.spl"] {
        let entry = cli_dir.join(entry_name);
        std::fs::write(&entry, "fn main() -> i64: 0\n").unwrap();
        let builder =
            NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join(format!("{entry_name}-out")))
                .config(NativeBuildConfig {
                    runtime_path: Some(runtime_path.clone()),
                    ..Default::default()
                })
                .entry_file(entry);
        let output_dir = temp.path().join(format!("{entry_name}-prepared"));
        let prepared = builder
            .prepare_stage4_compiler_backfill_archive(Some(&(provider.clone(), false)), &[], &output_dir)
            .unwrap()
            .unwrap();
        assert_eq!(prepared, output_dir.join("libsimple_compiler_backfill.a"));
        assert_ne!(prepared, dedicated);
        let (defined, _) = super::tools::archive_global_symbols(&prepared).unwrap();
        assert_eq!(defined.get("rt_cranelift_requested_hook"), Some(&1));
        assert!(!defined.contains_key("hidden_helper"));
    }

    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
}

#[cfg(target_os = "linux")]
#[test]
fn test_stage4_compiler_entries_force_fresh_core_c_over_runtime_path_decoys() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP", "1");
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
    }
    let temp = tempfile::tempdir().unwrap();
    let cli_dir = temp.path().join("src/app/cli");
    std::fs::create_dir_all(&cli_dir).unwrap();
    std::fs::write(temp.path().join("libsimple_native_all.a"), b"native-all-decoy").unwrap();
    let config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    for entry_name in ["main.spl", "native_build_main.spl"] {
        let entry = cli_dir.join(entry_name);
        std::fs::write(&entry, "fn main() -> i64: 0\n").unwrap();
        let builder =
            NativeProjectBuilder::new(temp.path().to_path_buf(), temp.path().join(format!("{entry_name}-out")))
                .config(config.clone())
                .entry_file(entry);
        let link_dir = temp.path().join(format!("{entry_name}-link"));
        let (selected, is_native_all) = builder.selected_runtime_library(&link_dir).unwrap().unwrap();
        assert_eq!(selected, link_dir.join("core_c_runtime/libsimple_runtime.a"));
        assert!(!is_native_all);
        assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    }

    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
}

#[test]
fn test_runtime_bundle_auto_ignores_native_all_for_non_compiler_entry() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };

    let mut builder = NativeProjectBuilder::new(
        PathBuf::from("/project"),
        PathBuf::from("/project/bin/t32_lsp_mcp_tool_runner"),
    )
    .config(config);
    builder.entry_file = Some(PathBuf::from(
        "/project/examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl",
    ));

    let selected_runtime = builder.selected_runtime_library(temp.path()).unwrap();
    assert!(selected_runtime.is_none());
    builder.reject_unexpected_native_all(selected_runtime.as_ref()).unwrap();
}

#[test]
fn test_runtime_bundle_hosted_is_removed_for_non_compiler_entry() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "hosted".to_string();

    let mut builder = NativeProjectBuilder::new(
        PathBuf::from("/project"),
        PathBuf::from("/project/bin/t32_lsp_mcp_tool_runner"),
    )
    .config(config);
    builder.entry_file = Some(PathBuf::from(
        "/project/examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl",
    ));

    let err = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(err.contains("removed Rust-hosted runtime bundles"));
}

#[test]
fn test_runtime_bundle_hosted_is_allowed_for_bootstrap_entry_only() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", "1") };
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "rust-hosted".to_string();
    let mut builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("simple")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/bootstrap_main.spl"));

    let selected = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_eq!(selected, (native_all, true));
    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
}

#[test]
fn test_core_c_bootstrap_entry_builds_runtime_when_explicit_path_has_only_native_all() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", "1") };
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "core-c-bootstrap".to_string();
    let mut builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("simple")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/bootstrap_main.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_ne!(selected, native_all);
    assert!(runtime_archive_has_bootstrap_cli_symbols(&selected));
    assert!(!is_native_all);
    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
}

#[cfg(target_os = "linux")]
#[test]
fn test_runtime_bundle_host_gpu_rejects_missing_engine2d_queue_symbols() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    build_compiler_backfill_test_archive(
        temp.path(),
        "simple_runtime",
        &["void rt_host_gpu_queue_reset(void) {}\n"],
    );

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "host-gpu".to_string();
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("engine2d")).config(config);

    let error = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(error.contains("missing Engine2D queue symbols"));
    assert!(error.contains("rt_host_gpu_queue_emit_payload"));
    assert!(error.contains("rt_host_gpu_queue_emit_payload_text"));
}

#[cfg(target_os = "linux")]
#[test]
fn test_runtime_bundle_host_gpu_discovers_cargo_deps_runtime_archive() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let deps = temp.path().join("deps");
    std::fs::create_dir_all(&deps).unwrap();
    build_compiler_backfill_test_archive(&deps, "simple_runtime", &["void rt_host_gpu_queue_reset(void) {}\n"]);

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "host-gpu".to_string();
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("engine2d")).config(config);

    let error = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(error.contains("missing Engine2D queue symbols"));
    assert!(!error.contains("feature-built libsimple_runtime.a is missing"));
}

#[test]
fn test_runtime_bundle_hosted_is_rejected_without_full_stage4_authorization() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let old_bootstrap = std::env::var_os("SIMPLE_BOOTSTRAP");
    let old_stage4 = std::env::var_os("SIMPLE_BOOTSTRAP_STAGE4");
    unsafe {
        std::env::remove_var("SIMPLE_BOOTSTRAP");
        std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", "1");
    }
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "rust-hosted".to_string();
    let mut builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("simple")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/main.spl"));

    let error = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(error.contains("removed Rust-hosted runtime bundles"));
    match old_stage4 {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP_STAGE4", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP_STAGE4") },
    }
    match old_bootstrap {
        Some(value) => unsafe { std::env::set_var("SIMPLE_BOOTSTRAP", value) },
        None => unsafe { std::env::remove_var("SIMPLE_BOOTSTRAP") },
    }
}

#[test]
fn test_runtime_bundle_core_c_bootstrap_alias_prefers_runtime_for_non_compiler_entry() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "core-c-bootstrap".to_string();

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/t32_mcp_native"))
            .config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/demo/app.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_eq!(selected, runtime);
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_simple_core_prefers_simple_core_archive_when_available() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let simple_core_dir = temp.path().join("simple-core");
    std::fs::create_dir_all(&simple_core_dir).unwrap();
    let simple_core = simple_core_dir.join("libsimple_runtime.a");
    let core_c = temp.path().join("libsimple_runtime.a");
    std::fs::write(&simple_core, b"simple-core").unwrap();
    std::fs::write(&core_c, b"core-c").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "simple-core".to_string();

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/hello_native")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/demo/app.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap().unwrap();
    assert_eq!(selected, simple_core);
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_simple_core_errors_when_archive_is_missing() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    std::fs::write(&runtime, b"core-c").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "simple-core".to_string();

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/hello_native")).config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/demo/app.spl"));

    let err = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(err.contains("no simple-core runtime archive"));
    assert!(err.contains("core-c-bootstrap"));
}

#[test]
fn test_runtime_bundle_legacy_all_alias_is_removed() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig {
        runtime_path: Some(temp.path().to_path_buf()),
        ..Default::default()
    };
    config.runtime_bundle = "all".to_string();

    let mut builder = NativeProjectBuilder::new(
        PathBuf::from("/project"),
        PathBuf::from("/project/bin/t32_lsp_mcp_tool_runner"),
    )
    .config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/demo/app.spl"));

    let err = builder.selected_runtime_library(temp.path()).unwrap_err();
    assert!(err.contains("removed Rust-hosted runtime bundles"));
}

#[test]
fn test_freestanding_linker_uses_c_compiler_without_runtime_bundle_probe() {
    let temp = tempfile::tempdir().unwrap();
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), temp.path().join("kernel.elf")).config(
        NativeBuildConfig {
            target: Some(simple_common::target::Target::new(
                simple_common::target::TargetArch::Riscv64,
                simple_common::target::TargetOS::None,
            )),
            ..Default::default()
        },
    );

    let cc = super::tools::find_c_compiler();
    let cxx = super::tools::find_cxx_compiler();

    assert!(!cc.is_empty());
    if cc != cxx {
        assert_ne!(cc, cxx);
    }
    assert!(builder.config.target.is_some());
}

#[test]
fn test_build_use_map_glob_import_populates_symbol_entries() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(lib_root.join("nogc_async_mut_noalloc/log")).unwrap();

    let logger_path = lib_root.join("nogc_async_mut_noalloc/log/logger.spl");
    let consumer_path = src_root.join("app/consumer.spl");
    std::fs::create_dir_all(consumer_path.parent().unwrap()).unwrap();

    std::fs::write(&logger_path, "fn log_info(msg: text):\n    pass\n").unwrap();
    std::fs::write(
        &consumer_path,
        "use lib.nogc_async_mut_noalloc.log.*\nfn main():\n    log_info(\"x\")\n",
    )
    .unwrap();

    let file_sources = vec![
        (logger_path.clone(), std::fs::read_to_string(&logger_path).unwrap()),
        (consumer_path.clone(), std::fs::read_to_string(&consumer_path).unwrap()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
    let expected = format!("{}__log_info", module_prefix_from_path(&logger_path, &lib_root));

    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&consumer_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&ast, &result.all_mangled, &result.re_exports);

    assert_eq!(use_map.get("log_info"), Some(&expected));
}

#[test]
fn test_build_use_map_keeps_production_check_modules() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let app_root = src_root.join("app");
    let check_path = app_root.join("cli/check.spl");
    let consumer_path = app_root.join("cli/main.spl");
    std::fs::create_dir_all(check_path.parent().unwrap()).unwrap();

    std::fs::write(&check_path, "fn run_check(args: [text]) -> i64:\n    return 0\n").unwrap();
    std::fs::write(
        &consumer_path,
        "use app.cli.check.{run_check}\nfn main() -> i64:\n    return run_check([])\n",
    )
    .unwrap();

    let file_sources = vec![
        (check_path.clone(), std::fs::read_to_string(&check_path).unwrap()),
        (consumer_path.clone(), std::fs::read_to_string(&consumer_path).unwrap()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&app_root), &src_root);
    let expected = format!("{}__run_check", module_prefix_from_path(&check_path, &app_root));
    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&consumer_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&ast, &result.all_mangled, &result.re_exports);

    assert_eq!(use_map.get("run_check"), Some(&expected));
}

#[test]
fn test_package_bare_exports_resolve_exact_cfg_active_sibling_owners() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let app_root = src_root.join("app");
    let pkg_root = app_root.join("pkg");
    std::fs::create_dir_all(&pkg_root).unwrap();

    let main_path = app_root.join("main.spl");
    let init_path = pkg_root.join("__init__.spl");
    let direct_path = pkg_root.join("direct.spl");
    let facade_path = pkg_root.join("facade.spl");
    let forward_path = pkg_root.join("forward.spl");
    let real_path = app_root.join("z_real.spl");
    let decoy_path = app_root.join("a_decoy.spl");
    let cfg_path = app_root.join("b_cfg_noise.spl");
    let private_path = pkg_root.join("private.spl");

    std::fs::write(
        &main_path,
        "use app.pkg.{direct_api, forwarded_api}\nuse app.pkg.private.{private_anchor}\nuse app.a_decoy.{decoy_anchor}\nuse app.b_cfg_noise.{cfg_anchor}\nfn main() -> i64:\n    return direct_api() + forwarded_api() + private_anchor() + decoy_anchor() + cfg_anchor()\n",
    )
    .unwrap();
    std::fs::write(&init_path, "export direct_api, forwarded_api, facade_anchor\n").unwrap();
    std::fs::write(
        &direct_path,
        "fn direct_api() -> i64:\n    return 7\nexport direct_api\n",
    )
    .unwrap();
    std::fs::write(
        &facade_path,
        "use app.pkg.direct.{direct_api}\nfn facade_anchor() -> i64:\n    return direct_api()\nexport direct_api, facade_anchor\n",
    )
    .unwrap();
    std::fs::write(&forward_path, "export use app.z_real.*\n").unwrap();
    std::fs::write(&real_path, "fn forwarded_api() -> i64:\n    return 11\n").unwrap();
    std::fs::write(
        &decoy_path,
        "fn direct_api() -> i64:\n    return 99\nfn forwarded_api() -> i64:\n    return 99\nfn decoy_anchor() -> i64:\n    return 0\n",
    )
    .unwrap();
    let inactive_arch = if super::effective_target().arch == simple_common::target::TargetArch::X86_64 {
        "riscv64"
    } else {
        "x86_64"
    };
    std::fs::write(
        &cfg_path,
        format!(
            "@cfg({inactive_arch})\nfn direct_api() -> i64:\n    return 88\n@cfg({inactive_arch})\nfn forwarded_api() -> i64:\n    return 88\nfn cfg_anchor() -> i64:\n    return 0\n"
        ),
    )
    .unwrap();
    std::fs::write(
        &private_path,
        "use app.a_decoy.{forwarded_api}\nfn direct_api() -> i64:\n    return 77\nfn private_anchor() -> i64:\n    return 0\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), temp.path().join("out"))
        .source_dir(src_root.clone())
        .entry_file(main_path.clone());
    let file_sources = builder.discover_reachable_files_with_sources(&main_path).unwrap();
    let actual: std::collections::BTreeSet<_> = file_sources
        .iter()
        .map(|(path, _)| path.strip_prefix(&src_root).unwrap().to_path_buf())
        .collect();
    let expected: std::collections::BTreeSet<_> = [
        "app/main.spl",
        "app/pkg/__init__.spl",
        "app/pkg/direct.spl",
        "app/pkg/facade.spl",
        "app/pkg/forward.spl",
        "app/pkg/private.spl",
        "app/z_real.spl",
        "app/a_decoy.spl",
        "app/b_cfg_noise.spl",
    ]
    .into_iter()
    .map(PathBuf::from)
    .collect();
    assert_eq!(actual, expected);

    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&src_root), &src_root);
    let direct_owner = format!("{}__direct_api", module_prefix_from_path(&direct_path, &src_root));
    let forwarded_owner = format!("{}__forwarded_api", module_prefix_from_path(&real_path, &src_root));
    let package_exports = result.re_exports.get("app__pkg").unwrap();
    assert_eq!(package_exports.get("direct_api"), Some(&direct_owner));
    assert_eq!(package_exports.get("forwarded_api"), Some(&forwarded_owner));
    assert_eq!(result.all_mangled.get("direct_api").unwrap().len(), 3);
    assert_eq!(result.all_mangled.get("forwarded_api").unwrap().len(), 2);
    assert!(result
        .re_exports
        .get(&module_prefix_from_path(&private_path, &src_root))
        .is_none_or(|exports| !exports.contains_key("forwarded_api")));

    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&main_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&ast, &result.all_mangled, &result.re_exports);
    assert_eq!(use_map.get("direct_api"), Some(&direct_owner));
    assert_eq!(use_map.get("forwarded_api"), Some(&forwarded_owner));

    let conflict_pkg = app_root.join("conflict_pkg");
    std::fs::create_dir_all(&conflict_pkg).unwrap();
    let conflict_paths = [
        (conflict_pkg.join("__init__.spl"), "export clash\n"),
        (conflict_pkg.join("a_forward.spl"), "export use app.real_a.{clash}\n"),
        (conflict_pkg.join("b_forward.spl"), "export use app.z_hop.{clash}\n"),
        (app_root.join("z_hop.spl"), "export use app.real_b.{clash}\n"),
        (app_root.join("real_a.spl"), "fn clash() -> i64:\n    return 1\n"),
        (app_root.join("real_b.spl"), "fn clash() -> i64:\n    return 2\n"),
        (
            app_root.join("conflict_consumer.spl"),
            "use app.conflict_pkg.{clash}\nfn consume() -> i64:\n    return clash()\n",
        ),
    ];
    for (path, source) in &conflict_paths {
        std::fs::write(path, source).unwrap();
    }
    let conflict_sources: Vec<_> = conflict_paths
        .iter()
        .map(|(path, _)| (path.clone(), std::fs::read_to_string(path).unwrap()))
        .collect();
    let conflict = super::imports::build_import_map(&conflict_sources, std::slice::from_ref(&src_root), &src_root);
    let real_a = format!(
        "{}__clash",
        module_prefix_from_path(&app_root.join("real_a.spl"), &src_root)
    );
    let real_b = format!(
        "{}__clash",
        module_prefix_from_path(&app_root.join("real_b.spl"), &src_root)
    );
    assert_eq!(
        conflict
            .re_exports
            .get("app__conflict_pkg__a_forward")
            .and_then(|exports| exports.get("clash")),
        Some(&real_a)
    );
    assert_eq!(
        conflict
            .re_exports
            .get("app__conflict_pkg__b_forward")
            .and_then(|exports| exports.get("clash")),
        Some(&real_b)
    );
    assert!(conflict
        .re_exports
        .get("app__conflict_pkg")
        .is_none_or(|exports| !exports.contains_key("clash")));
    let consumer_ast = simple_parser::Parser::new(&conflict_sources.last().unwrap().1)
        .parse()
        .unwrap();
    let conflict_use_map =
        super::imports::build_use_map_from_ast(&consumer_ast, &conflict.all_mangled, &conflict.re_exports);
    assert!(!conflict_use_map.contains_key("clash"));

    let star_pkg = app_root.join("star_pkg");
    std::fs::create_dir_all(&star_pkg).unwrap();
    std::fs::write(star_pkg.join("__init__.spl"), "export *\n").unwrap();
    let star_main = app_root.join("star_main.spl");
    std::fs::write(&star_main, "use app.star_pkg.*\nfn main():\n    pass\n").unwrap();
    let star_error = builder.discover_reachable_files_with_sources(&star_main).unwrap_err();
    assert!(star_error.contains("bare package `export *` is unsupported"));
}

#[test]
fn test_entry_closure_and_use_map_follow_nested_function_local_use() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let main_path = src_root.join("app/main.spl");
    let worker_path = src_root.join("app/worker.spl");
    let codec_path = src_root.join("lib/local_codec.spl");
    std::fs::create_dir_all(main_path.parent().unwrap()).unwrap();
    std::fs::create_dir_all(codec_path.parent().unwrap()).unwrap();
    std::fs::write(
        &main_path,
        "use app.worker.{run_worker}\nfn main() -> i64:\n    return run_worker(true)\n",
    )
    .unwrap();
    std::fs::write(
        &worker_path,
        "fn run_worker(enabled: bool) -> i64:\n    if enabled:\n        val action = \\:\n            use lib.local_codec.{encode_local_value}\n            encode_local_value()\n        return action()\n    return 0\n",
    )
    .unwrap();
    std::fs::write(&codec_path, "fn encode_local_value() -> i64:\n    return 7\n").unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), temp.path().join("out"))
        .source_dir(src_root.clone())
        .entry_file(main_path.clone());
    let file_sources = builder.discover_reachable_files_with_sources(&main_path).unwrap();
    let actual: std::collections::BTreeSet<_> = file_sources
        .iter()
        .map(|(path, _)| path.strip_prefix(&src_root).unwrap().to_path_buf())
        .collect();
    let expected: std::collections::BTreeSet<_> = ["app/main.spl", "app/worker.spl", "lib/local_codec.spl"]
        .into_iter()
        .map(PathBuf::from)
        .collect();
    assert_eq!(actual, expected);

    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&src_root), &src_root);
    let worker_ast = simple_parser::Parser::new(&std::fs::read_to_string(&worker_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&worker_ast, &result.all_mangled, &result.re_exports);
    let owner = format!(
        "{}__encode_local_value",
        module_prefix_from_path(&codec_path, &src_root)
    );
    assert_eq!(use_map.get("encode_local_value"), Some(&owner));
}

#[test]
fn test_build_use_map_resolves_data_from_dotted_module_with_name_collision() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let app_root = src_root.join("app");
    let ansi_path = app_root.join("ui.render/ansi.spl");
    let colors_path = app_root.join("dashboard.render/colors.spl");
    let consumer_path = app_root.join("ui.tui/screen.spl");
    std::fs::create_dir_all(ansi_path.parent().unwrap()).unwrap();
    std::fs::create_dir_all(colors_path.parent().unwrap()).unwrap();
    std::fs::create_dir_all(consumer_path.parent().unwrap()).unwrap();

    std::fs::write(&ansi_path, "val RESET: text = \"ansi\"\n").unwrap();
    std::fs::write(&colors_path, "val RESET: text = \"dashboard\"\n").unwrap();
    std::fs::write(
        &consumer_path,
        "use app.ui.render.ansi.{RESET}\nfn main():\n    print RESET\n",
    )
    .unwrap();

    let file_sources = vec![
        (colors_path.clone(), std::fs::read_to_string(&colors_path).unwrap()),
        (ansi_path.clone(), std::fs::read_to_string(&ansi_path).unwrap()),
        (consumer_path.clone(), std::fs::read_to_string(&consumer_path).unwrap()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&app_root), &src_root);
    let expected = format!("{}__RESET", module_prefix_from_path(&ansi_path, &app_root));
    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&consumer_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&ast, &result.all_mangled, &result.re_exports);

    assert_eq!(use_map.get("RESET"), Some(&expected));
}

#[test]
fn test_build_import_map_skips_pass_only_trait_methods() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(lib_root.join("common")).unwrap();

    let trait_path = lib_root.join("common/reader.spl");
    std::fs::write(
        &trait_path,
        "trait Reader:\n    fn path(self) -> text:\n        pass\n    fn label(self) -> text:\n        return \"reader\"\n",
    )
    .unwrap();

    let file_sources = vec![(trait_path.clone(), std::fs::read_to_string(&trait_path).unwrap())];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
    let prefix = module_prefix_from_path(&trait_path, &lib_root);

    assert!(!result.all_mangled.contains_key("Reader.path"));
    assert!(!result.all_mangled.contains_key("path"));
    assert_eq!(
        result.all_mangled.get("Reader.label"),
        Some(&vec![format!("{}__Reader_dot_label", prefix)])
    );
}

#[test]
fn test_build_import_map_records_concrete_method_arities() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    let path = lib_root.join("core/methods.spl");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(
        &path,
        "trait Iterator:\n    fn missing():\n        pass\n    fn count() -> i64:\n        return 0\n\nstruct Tensor:\n    fn T(self) -> i64:\n        return 1\n",
    )
    .unwrap();

    let file_sources = vec![(path.clone(), std::fs::read_to_string(&path).unwrap())];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
    let prefix = module_prefix_from_path(&path, &lib_root);

    assert_eq!(
        result.fn_arities.get(&format!("{}__Iterator_dot_count", prefix)),
        Some(&1)
    );
    assert_eq!(result.fn_arities.get(&format!("{}__Tensor_dot_T", prefix)), Some(&1));
    assert!(!result
        .fn_arities
        .contains_key(&format!("{}__Iterator_dot_missing", prefix)));
}

#[test]
fn test_build_import_map_records_cross_module_trait_implementations() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    let trait_path = lib_root.join("fs/block_device.spl");
    let impl_path = lib_root.join("fs/mem_block_device.spl");
    std::fs::create_dir_all(trait_path.parent().unwrap()).unwrap();
    std::fs::write(&trait_path, "trait BlockDevice:\n    fn sector_size() -> u32\n").unwrap();
    std::fs::write(
        &impl_path,
        "struct MemBlockDevice:\n    size: u32\n\nimpl BlockDevice for MemBlockDevice:\n    fn sector_size() -> u32:\n        self.size\n",
    )
    .unwrap();

    let file_sources = vec![
        (trait_path.clone(), std::fs::read_to_string(&trait_path).unwrap()),
        (impl_path.clone(), std::fs::read_to_string(&impl_path).unwrap()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);

    assert_eq!(
        result.trait_impls.get("BlockDevice"),
        Some(&vec!["MemBlockDevice".to_string()])
    );
}

#[test]
fn test_build_import_map_records_optional_struct_return_types() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let os_root = src_root.join("os");
    let mapping_path = os_root.join("kernel/mapping.spl");
    std::fs::create_dir_all(mapping_path.parent().unwrap()).unwrap();
    std::fs::write(
        &mapping_path,
        "struct MemoryRuntimeMapping:\n    allocation_id: u64\n    owner_id: u64\n\nfn find_mapping(id: u64) -> MemoryRuntimeMapping?:\n    nil\n",
    )
    .unwrap();

    let file_sources = vec![(mapping_path.clone(), std::fs::read_to_string(&mapping_path).unwrap())];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&os_root), &src_root);

    assert_eq!(
        result.fn_return_types.get("find_mapping"),
        Some(&simple_parser::Type::Optional(Box::new(simple_parser::Type::Simple(
            "MemoryRuntimeMapping".to_string()
        ))))
    );
}

#[test]
fn test_build_import_map_records_primitive_return_types() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let os_root = src_root.join("os");
    let vmm_path = os_root.join("kernel/memory/vmm_core.spl");
    std::fs::create_dir_all(vmm_path.parent().unwrap()).unwrap();
    std::fs::write(&vmm_path, "fn vmm_read_pte(addr: u64) -> u64:\n    addr\n").unwrap();

    let file_sources = vec![(vmm_path.clone(), std::fs::read_to_string(&vmm_path).unwrap())];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&os_root), &src_root);

    assert_eq!(
        result.fn_return_types.get("vmm_read_pte"),
        Some(&simple_parser::Type::Simple("u64".to_string()))
    );
}

#[test]
fn test_global_primitive_return_keeps_native_comparison_typed() {
    let source = "struct SwapTxn:\n    source_phys_addr: u64\n\nfn changed(txn: SwapTxn) -> bool:\n    val current = vmm_read_pte(0)\n    return current != txn.source_phys_addr\n";
    let ast = simple_parser::Parser::new(source).parse().unwrap();
    let mut lowerer = crate::hir::Lowerer::new();
    lowerer.set_lenient_types(true);
    lowerer.set_global_fn_return_types(std::sync::Arc::new(std::collections::HashMap::from([(
        "vmm_read_pte".to_string(),
        simple_parser::Type::Simple("u64".to_string()),
    )])));

    let lowered = lowerer.lower_module(&ast).unwrap();
    let changed = lowered
        .functions
        .iter()
        .find(|function| function.name == "changed")
        .unwrap();
    let current = changed.locals.iter().find(|local| local.name == "current").unwrap();
    assert_eq!(current.ty, crate::hir::TypeId::U64);
    let crate::hir::HirStmt::Return(Some(expr)) = &changed.body[1] else {
        panic!("expected comparison return");
    };
    let crate::hir::HirExprKind::Binary { left, right, .. } = &expr.kind else {
        panic!("expected binary comparison");
    };
    assert_eq!(left.ty, crate::hir::TypeId::U64);
    assert_eq!(right.ty, crate::hir::TypeId::U64);
}

#[test]
fn test_cross_module_optional_struct_match_keeps_payload_type() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let os_root = src_root.join("os");
    let memory_root = os_root.join("kernel/memory");
    std::fs::create_dir_all(&memory_root).unwrap();

    let manager_path = memory_root.join("memory_leveling_manager.spl");
    let runtime_path = memory_root.join("memory_leveling_runtime.spl");
    let caller_path = memory_root.join("memory_swap_runtime.spl");
    std::fs::write(
        &manager_path,
        "struct MemoryRuntimeMapping:\n    allocation_id: u64\n    owner_id: u64\n",
    )
    .unwrap();
    std::fs::write(
        &runtime_path,
        "use os.kernel.memory.memory_leveling_manager.MemoryRuntimeMapping\n\nfn find_mapping(id: u64) -> MemoryRuntimeMapping?:\n    nil\n",
    )
    .unwrap();
    std::fs::write(
        &caller_path,
        "use os.kernel.memory.memory_leveling_runtime.find_mapping\n\nfn owner() -> u64:\n    match find_mapping(1):\n        Some(mapping):\n            return mapping.owner_id\n        None:\n            return 0\n",
    )
    .unwrap();

    let paths = [&manager_path, &runtime_path, &caller_path];
    let file_sources: Vec<_> = paths
        .iter()
        .map(|path| ((*path).clone(), std::fs::read_to_string(path).unwrap()))
        .collect();
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&os_root), &src_root);

    let mut field_indices: std::collections::HashMap<String, std::collections::HashSet<usize>> =
        std::collections::HashMap::new();
    for fields in result.struct_defs.values() {
        for (index, (field_name, _)) in fields.iter().enumerate() {
            field_indices.entry(field_name.clone()).or_default().insert(index);
        }
    }
    let ambiguous = field_indices
        .into_iter()
        .filter_map(|(name, indices)| (indices.len() > 1).then_some(name))
        .collect();

    let caller_source = std::fs::read_to_string(&caller_path).unwrap();
    let ast = simple_parser::Parser::new(&caller_source).parse().unwrap();
    let resolver = crate::module_resolver::ModuleResolver::new(project_root, os_root.clone())
        .with_extra_source_roots(vec![src_root, os_root]);
    let mut lowerer = crate::hir::Lowerer::with_module_resolver(resolver, caller_path);
    lowerer.set_lenient_types(true);
    lowerer.set_global_struct_defs(std::sync::Arc::new(result.struct_defs));
    lowerer.set_duplicate_global_struct_defs(std::sync::Arc::new(result.duplicate_struct_defs));
    lowerer.set_ambiguous_field_names(std::sync::Arc::new(ambiguous));
    lowerer.set_global_fn_return_types(std::sync::Arc::new(result.fn_return_types));

    let lowered = lowerer.lower_module(&ast).unwrap();
    let owner = lowered
        .functions
        .iter()
        .find(|function| function.name == "owner")
        .unwrap();
    let mapping = owner.locals.iter().find(|local| local.name == "mapping").unwrap();
    assert!(matches!(
        lowered.types.get(mapping.ty),
        Some(crate::hir::HirType::Struct { name, .. }) if name == "MemoryRuntimeMapping"
    ));
    assert!(
        format!("{:?}", owner.body).contains("rt_enum_payload"),
        "materialized Option payload must be extracted before struct field access"
    );
}

#[test]
fn test_build_import_map_records_enum_defs_without_callable_variant_symbols() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(lib_root.join("types")).unwrap();

    let enum_path = lib_root.join("types/inference.spl");
    std::fs::write(
        &enum_path,
        "enum Type:\n    Int(bits: i32, signed: bool)\n    Var(id: i64)\n",
    )
    .unwrap();

    let file_sources = vec![(enum_path.clone(), std::fs::read_to_string(&enum_path).unwrap())];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);

    assert!(result.all_mangled.contains_key("Type"));
    assert!(!result.all_mangled.contains_key("Type.Int"));
    assert!(!result.all_mangled.contains_key("Type.Var"));
    assert_eq!(
        result.enum_defs.get("Type"),
        Some(&vec![
            (
                "Int".to_string(),
                Some(vec![
                    simple_parser::Type::Simple("i32".to_string()),
                    simple_parser::Type::Simple("bool".to_string()),
                ]),
            ),
            (
                "Var".to_string(),
                Some(vec![simple_parser::Type::Simple("i64".to_string())]),
            ),
        ])
    );
}

#[test]
fn test_duplicate_global_enum_payload_types_are_erased() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(&lib_root).unwrap();
    let left = lib_root.join("left.spl");
    let right = lib_root.join("right.spl");
    let left_source = "enum Envelope:\n    Value(value: LeftKind)\n    Empty\n";
    let right_source = "enum Envelope:\n    Value(value: RightKind)\n    Empty\n";
    std::fs::write(&left, left_source).unwrap();
    std::fs::write(&right, right_source).unwrap();

    for file_sources in [
        vec![
            (left.clone(), left_source.to_string()),
            (right.clone(), right_source.to_string()),
        ],
        vec![
            (right.clone(), right_source.to_string()),
            (left.clone(), left_source.to_string()),
        ],
    ] {
        let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
        assert_eq!(
            result.enum_defs.get("Envelope"),
            Some(&vec![
                (
                    "Value".to_string(),
                    Some(vec![simple_parser::Type::Simple("Any".to_string())]),
                ),
                ("Empty".to_string(), None),
            ])
        );
    }
}

#[test]
fn test_ambiguous_global_payload_owners_are_erased_in_both_orders() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(&lib_root).unwrap();
    let left = lib_root.join("left.spl");
    let right = lib_root.join("right.spl");
    let envelope = lib_root.join("envelope.spl");
    let left_source = "enum MemorySpace:\n    Shared\n\nstruct Point:\n    x: i64\n";
    let right_source = "enum MemorySpace:\n    Private\n\nstruct Point:\n    y: bool\n";
    let envelope_source = "enum Envelope:\n    Space(value: MemorySpace)\n    Location(value: Point)\n";

    for file_sources in [
        vec![
            (envelope.clone(), envelope_source.to_string()),
            (left.clone(), left_source.to_string()),
            (right.clone(), right_source.to_string()),
        ],
        vec![
            (right.clone(), right_source.to_string()),
            (left.clone(), left_source.to_string()),
            (envelope.clone(), envelope_source.to_string()),
        ],
    ] {
        let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
        assert_eq!(
            result.enum_defs.get("Envelope"),
            Some(&vec![
                (
                    "Space".to_string(),
                    Some(vec![simple_parser::Type::Simple("Any".to_string())]),
                ),
                (
                    "Location".to_string(),
                    Some(vec![simple_parser::Type::Simple("Any".to_string())]),
                ),
            ])
        );
    }
}

#[test]
fn test_duplicate_global_enum_unit_payload_conflict_is_not_order_dependent() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(&lib_root).unwrap();
    let left = lib_root.join("left.spl");
    let right = lib_root.join("right.spl");
    let left_source = "enum Envelope:\n    Empty\n";
    let right_source = "enum Envelope:\n    Empty(value: i64)\n";

    for file_sources in [
        vec![
            (left.clone(), left_source.to_string()),
            (right.clone(), right_source.to_string()),
        ],
        vec![
            (right.clone(), right_source.to_string()),
            (left.clone(), left_source.to_string()),
        ],
    ] {
        let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
        assert_eq!(
            result.enum_defs.get("Envelope"),
            Some(&vec![(
                "Empty".to_string(),
                Some(vec![simple_parser::Type::Simple("Any".to_string())]),
            )])
        );
    }
}

#[test]
fn test_global_enum_payload_keeps_nested_enum_owner() {
    let temp = tempfile::tempdir().unwrap();
    let src_root = temp.path().join("project/src");
    let lib_root = src_root.join("lib");
    std::fs::create_dir_all(&lib_root).unwrap();

    let types_path = lib_root.join("types.spl");
    std::fs::write(
        &types_path,
        "enum MemorySpace:\n    Shared\n    Private\n\nenum Envelope:\n    Space(value: MemorySpace)\n    Empty\n",
    )
    .unwrap();
    let consumer_path = src_root.join("consumer.spl");
    let consumer_source = "fn describe(value: Envelope) -> text:\n    match value:\n        case Envelope.Space(space):\n            match space:\n                case Shared:\n                    return \"shared\"\n                case Private:\n                    return \"private\"\n        case Envelope.Empty:\n            return \"empty\"\n";
    std::fs::write(&consumer_path, consumer_source).unwrap();

    let file_sources = vec![
        (types_path.clone(), std::fs::read_to_string(&types_path).unwrap()),
        (consumer_path.clone(), consumer_source.to_string()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&lib_root), &src_root);
    let ast = simple_parser::Parser::new(consumer_source).parse().unwrap();
    let mut lowerer = crate::hir::Lowerer::new();
    lowerer.set_global_enum_defs(std::sync::Arc::new(result.enum_defs));
    lowerer.register_global_enums();

    let lowered = lowerer
        .lower_module(&ast)
        .expect("nested imported enum payload should lower");
    let function = lowered
        .functions
        .iter()
        .find(|function| function.name == "describe")
        .unwrap();
    let space = function.locals.iter().find(|local| local.name == "space").unwrap();
    assert!(matches!(
        lowered.types.get(space.ty),
        Some(crate::hir::HirType::Enum { name, .. }) if name == "MemorySpace"
    ));
    let hir = format!("{:?}", function.body);
    assert!(hir.contains("rt_enum_payload"), "{hir}");
    assert!(!hir.contains("Global(\"Shared\")"), "{hir}");

    let mir = crate::mir::lower_to_mir(&lowered).expect("nested imported enum payload should reach MIR");
    let mir = format!("{mir:?}");
    assert!(!mir.contains("global_name: \"Shared\""), "{mir}");
}

#[test]
fn test_llvm_mangle_renames_imported_global_declarations_with_uses() {
    let mut mir = crate::mir::MirModule::new();
    mir.globals
        .push(("MAX_TASKS".to_string(), crate::hir::TypeId::I64, false));
    let mut func = crate::mir::MirFunction::new(
        "main".to_string(),
        crate::hir::TypeId::VOID,
        simple_parser::Visibility::Private,
    );
    func.blocks[0].instructions.push(crate::mir::MirInst::GlobalLoad {
        dest: crate::mir::VReg(0),
        global_name: "MAX_TASKS".to_string(),
        ty: crate::hir::TypeId::I64,
    });
    func.blocks[0].terminator = crate::mir::Terminator::Return(None);
    mir.functions.push(func);

    let mut use_map = std::collections::HashMap::new();
    use_map.insert(
        "MAX_TASKS".to_string(),
        "os__kernel__scheduler__scheduler_types__MAX_TASKS".to_string(),
    );

    let unresolved = super::mangle::mangle_mir(
        &mut mir,
        "app__entry",
        true,
        &std::collections::HashMap::new(),
        &std::collections::HashSet::new(),
        &use_map,
        &std::collections::HashMap::new(),
    );

    assert_eq!(unresolved, 0);
    assert_eq!(mir.globals[0].0, "os__kernel__scheduler__scheduler_types__MAX_TASKS");
    match &mir.functions[0].blocks[0].instructions[0] {
        crate::mir::MirInst::GlobalLoad { global_name, .. } => {
            assert_eq!(global_name, "os__kernel__scheduler__scheduler_types__MAX_TASKS")
        }
        other => panic!("expected global load, got {other:?}"),
    }
}

#[test]
fn test_llvm_mangle_does_not_rebind_qualified_method_to_unrelated_type() {
    let mut mir = crate::mir::MirModule::new();
    let mut func = crate::mir::MirFunction::new(
        "main".to_string(),
        crate::hir::TypeId::VOID,
        simple_parser::Visibility::Private,
    );
    func.blocks[0].instructions.push(crate::mir::MirInst::MethodCallStatic {
        dest: Some(crate::mir::VReg(1)),
        receiver: crate::mir::VReg(0),
        func_name: "str.rfind".to_string(),
        args: vec![],
    });
    func.blocks[0].terminator = crate::mir::Terminator::Return(None);
    mir.functions.push(func);

    let suffix_index = std::collections::HashMap::from([(
        "rfind".to_string(),
        vec!["core__traits__DoubleEndedIterator_dot_rfind".to_string()],
    )]);
    super::mangle::mangle_mir(
        &mut mir,
        "app__entry",
        true,
        &std::collections::HashMap::new(),
        &std::collections::HashSet::new(),
        &std::collections::HashMap::new(),
        &suffix_index,
    );

    match &mir.functions[0].blocks[0].instructions[0] {
        crate::mir::MirInst::MethodCallStatic { func_name, .. } => {
            assert_eq!(func_name, "str.rfind");
        }
        other => panic!("expected static method call, got {other:?}"),
    }
}

#[test]
fn test_llvm_mangle_does_not_rebind_qualified_string_builtin_to_imported_wrapper() {
    let mut mir = crate::mir::MirModule::new();
    let mut func = crate::mir::MirFunction::new(
        "str_ends_with".to_string(),
        crate::hir::TypeId::BOOL,
        simple_parser::Visibility::Private,
    );
    func.blocks[0].instructions.push(crate::mir::MirInst::MethodCallStatic {
        dest: Some(crate::mir::VReg(2)),
        receiver: crate::mir::VReg(0),
        func_name: "str.ends_with".to_string(),
        args: vec![crate::mir::VReg(1)],
    });
    func.blocks[0].terminator = crate::mir::Terminator::Return(Some(crate::mir::VReg(2)));
    mir.functions.push(func);

    let use_map = std::collections::HashMap::from([(
        "str.ends_with".to_string(),
        "common__string_core__str_ends_with".to_string(),
    )]);
    super::mangle::mangle_mir(
        &mut mir,
        "common__string_core",
        false,
        &std::collections::HashMap::new(),
        &std::collections::HashSet::new(),
        &use_map,
        &std::collections::HashMap::new(),
    );

    match &mir.functions[0].blocks[0].instructions[0] {
        crate::mir::MirInst::MethodCallStatic { func_name, .. } => {
            assert_eq!(func_name, "str.ends_with");
        }
        other => panic!("expected static method call, got {other:?}"),
    }
}

#[test]
fn test_llvm_mangle_resolves_desugared_cross_module_method() {
    let mut mir = crate::mir::MirModule::new();
    let mut func = crate::mir::MirFunction::new(
        "main".to_string(),
        crate::hir::TypeId::VOID,
        simple_parser::Visibility::Private,
    );
    func.blocks[0].instructions.push(crate::mir::MirInst::MethodCallStatic {
        dest: Some(crate::mir::VReg(1)),
        receiver: crate::mir::VReg(0),
        func_name: "TreeSitter.match_token".to_string(),
        args: vec![],
    });
    func.blocks[0].terminator = crate::mir::Terminator::Return(None);
    mir.functions.push(func);

    let import_map = std::collections::HashMap::from([(
        "treesitter_match_token".to_string(),
        "frontend__treesitter__outline_lexer__treesitter_match_token".to_string(),
    )]);
    super::mangle::mangle_mir(
        &mut mir,
        "frontend__treesitter__outline",
        true,
        &import_map,
        &std::collections::HashSet::new(),
        &std::collections::HashMap::new(),
        &std::collections::HashMap::new(),
    );

    match &mir.functions[0].blocks[0].instructions[0] {
        crate::mir::MirInst::MethodCallStatic { func_name, .. } => {
            assert_eq!(func_name, "frontend__treesitter__outline_lexer__treesitter_match_token")
        }
        other => panic!("expected static method call, got {other:?}"),
    }
}

#[test]
fn test_re_exports_include_glob_imported_facade_symbols() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let lib_root = src_root.join("lib");
    let os_root = src_root.join("os");
    std::fs::create_dir_all(lib_root.join("nogc_async_mut_noalloc/log")).unwrap();
    std::fs::create_dir_all(os_root.join("kernel/log")).unwrap();
    std::fs::create_dir_all(src_root.join("app")).unwrap();

    let logger_path = lib_root.join("nogc_async_mut_noalloc/log/logger.spl");
    let facade_path = os_root.join("kernel/log/klog_api.spl");
    let consumer_path = src_root.join("app/consumer.spl");

    std::fs::write(&logger_path, "fn log_info(msg: text):\n    pass\n").unwrap();
    std::fs::write(&facade_path, "use lib.nogc_async_mut_noalloc.log.*\nexport log_info\n").unwrap();
    std::fs::write(
        &consumer_path,
        "use os.kernel.log.klog_api.{log_info}\nfn main():\n    log_info(\"x\")\n",
    )
    .unwrap();

    let file_sources = vec![
        (logger_path.clone(), std::fs::read_to_string(&logger_path).unwrap()),
        (facade_path.clone(), std::fs::read_to_string(&facade_path).unwrap()),
        (consumer_path.clone(), std::fs::read_to_string(&consumer_path).unwrap()),
    ];
    let source_dirs = vec![lib_root.clone(), os_root.clone(), src_root.join("app")];
    let result = super::imports::build_import_map(&file_sources, &source_dirs, &src_root);
    let expected = format!("{}__log_info", module_prefix_from_path(&logger_path, &lib_root));
    let facade_prefix = module_prefix_from_path(&facade_path, &os_root);

    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&consumer_path).unwrap())
        .parse()
        .unwrap();
    let use_map = super::imports::build_use_map_from_ast(&ast, &result.all_mangled, &result.re_exports);

    assert_eq!(
        result
            .re_exports
            .get(&facade_prefix)
            .and_then(|exports| exports.get("log_info")),
        Some(&expected)
    );
    assert_eq!(use_map.get("log_info"), Some(&expected));
}

#[test]
fn test_package_selected_data_global_reaches_hir_and_mir() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let app = src_root.join("app");
    let package = src_root.join("app/pkg");
    let other = src_root.join("app/other");
    let transparent = package.join("_Split");
    let child = package.join("child");
    std::fs::create_dir_all(&package).unwrap();
    std::fs::create_dir_all(&other).unwrap();
    std::fs::create_dir_all(&transparent).unwrap();
    std::fs::create_dir_all(&child).unwrap();

    let parent_facade = app.join("__init__.spl");
    let parent_state = app.join("state.spl");
    let facade = package.join("__init__.spl");
    let state = package.join("state.spl");
    let reader = package.join("reader.spl");
    let transparent_reader = transparent.join("reader.spl");
    let child_reader = child.join("reader.spl");
    let clash_a = package.join("clash_a.spl");
    let clash_b = package.join("clash_b.spl");
    let clash_reader = package.join("clash_reader.spl");
    let typo = package.join("typo.spl");
    let unrelated = other.join("state.spl");
    std::fs::write(&parent_facade, "export PARENT_FLAG\n").unwrap();
    std::fs::write(&parent_state, "var PARENT_FLAG: bool = true\n").unwrap();
    std::fs::write(&facade, "export FLAG, DYNAMIC_FLAG, ITEM, read\n").unwrap();
    std::fs::write(
        &state,
        "struct Foo:\n    x: i64\nvar FLAG: bool = true\nvar PRIVATE_FLAG: bool = true\nvar DYNAMIC_FLAG = false\nvar ITEM: Foo = nil\n",
    )
    .unwrap();
    std::fs::write(
        &reader,
        "fn read() -> bool:\n    FLAG\nfn read_private() -> bool:\n    PRIVATE_FLAG\nfn read_parent() -> bool:\n    PARENT_FLAG\n",
    )
    .unwrap();
    std::fs::write(&transparent_reader, "fn read_private() -> bool:\n    PRIVATE_FLAG\n").unwrap();
    std::fs::write(&child_reader, "fn read_private() -> bool:\n    PRIVATE_FLAG\n").unwrap();
    std::fs::write(&clash_a, "var CLASH: i64 = 1\n").unwrap();
    std::fs::write(&clash_b, "var CLASH: i64 = 2\n").unwrap();
    std::fs::write(&clash_reader, "fn read_clash() -> i64:\n    CLASH\n").unwrap();
    std::fs::write(&typo, "fn typo() -> i64:\n    OUTSIDE_ONLY\n").unwrap();
    std::fs::write(
        &unrelated,
        "struct Foo:\n    y: text\nvar FLAG: i64 = 1\nvar OUTSIDE_ONLY: i64 = 9\n",
    )
    .unwrap();

    let paths = [
        &parent_facade,
        &parent_state,
        &facade,
        &state,
        &reader,
        &transparent_reader,
        &child_reader,
        &clash_a,
        &clash_b,
        &clash_reader,
        &typo,
        &unrelated,
    ];
    let file_sources: Vec<_> = paths
        .iter()
        .map(|path| ((*path).clone(), std::fs::read_to_string(path).unwrap()))
        .collect();
    let source_dirs = vec![src_root.clone()];
    let result = super::imports::build_import_map(&file_sources, &source_dirs, &src_root);
    let expected_owner = format!("{}__FLAG", module_prefix_from_path(&state, &src_root));
    let package_prefix = module_prefix_from_path(&package, &src_root);
    let private_owner = format!("{}__PRIVATE_FLAG", module_prefix_from_path(&state, &src_root));
    assert_eq!(
        result
            .package_data
            .get(&package_prefix)
            .and_then(|entries| entries.get("PRIVATE_FLAG")),
        Some(&private_owner)
    );
    assert!(!result
        .package_data
        .get(&package_prefix)
        .is_some_and(|entries| entries.contains_key("CLASH")));
    assert_eq!(
        result
            .re_exports
            .get(&package_prefix)
            .and_then(|exports| exports.get("FLAG")),
        Some(&expected_owner)
    );
    assert_eq!(
        result.data_types.get(&expected_owner),
        Some(&simple_parser::Type::Simple("bool".into()))
    );
    let dynamic_owner = format!("{}__DYNAMIC_FLAG", module_prefix_from_path(&state, &src_root));
    assert_eq!(
        result.data_types.get(&dynamic_owner),
        Some(&simple_parser::Type::Simple("Any".into()))
    );
    let item_owner = format!("{}__ITEM", module_prefix_from_path(&state, &src_root));
    assert_eq!(
        result.data_types.get(&item_owner),
        Some(&simple_parser::Type::Simple("Any".into()))
    );
    let parent_owner = format!("{}__PARENT_FLAG", module_prefix_from_path(&parent_state, &src_root));
    assert_eq!(
        result
            .re_exports
            .get(&module_prefix_from_path(&app, &src_root))
            .and_then(|exports| exports.get("PARENT_FLAG")),
        Some(&parent_owner)
    );

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(result.map),
        ambiguous_names: std::sync::Arc::new(result.ambiguous),
        all_mangled: std::sync::Arc::new(result.all_mangled),
        re_exports: std::sync::Arc::new(result.re_exports),
        trait_impls: std::sync::Arc::new(result.trait_impls),
        struct_defs: std::sync::Arc::new(result.struct_defs),
        duplicate_struct_defs: std::sync::Arc::new(result.duplicate_struct_defs),
        enum_defs: std::sync::Arc::new(result.enum_defs),
        data_exports: std::sync::Arc::new(result.data_exports),
        data_types: std::sync::Arc::new(result.data_types),
        package_data: std::sync::Arc::new(result.package_data),
        fn_arities: std::sync::Arc::new(result.fn_arities),
        fn_return_types: std::sync::Arc::new(result.fn_return_types),
        populate_global_struct_defs: true,
        populate_global_enum_defs: true,
    };

    let object = compile_file_to_object(
        &std::fs::read_to_string(&reader).unwrap(),
        &reader,
        &project_root,
        &src_root,
        &source_dirs,
        false,
        crate::optimizations::NativeOptimizationLevel::None,
        false,
        &imports,
    )
    .unwrap();
    assert!(!object.is_empty());

    let transparent_object = compile_file_to_object(
        &std::fs::read_to_string(&transparent_reader).unwrap(),
        &transparent_reader,
        &project_root,
        &src_root,
        &source_dirs,
        false,
        crate::optimizations::NativeOptimizationLevel::None,
        false,
        &imports,
    )
    .unwrap();
    assert!(!transparent_object.is_empty());

    for (path, missing) in [
        (&child_reader, "PRIVATE_FLAG"),
        (&clash_reader, "CLASH"),
        (&typo, "OUTSIDE_ONLY"),
    ] {
        let error = compile_file_to_object(
            &std::fs::read_to_string(path).unwrap(),
            path,
            &project_root,
            &src_root,
            &source_dirs,
            false,
            crate::optimizations::NativeOptimizationLevel::None,
            false,
            &imports,
        )
        .unwrap_err();
        assert!(error.contains(&format!("Undefined global `{missing}`")), "{error}");
    }
}

#[test]
fn test_duplicate_struct_sidecar_resolves_unique_compiler_context_handle() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let compiler_root = src_root.join("compiler");
    std::fs::create_dir_all(compiler_root.join("99.loader/loader")).unwrap();
    std::fs::create_dir_all(compiler_root.join("99.loader")).unwrap();
    std::fs::create_dir_all(compiler_root.join("70.backend/linker")).unwrap();

    let alive_ctx = compiler_root.join("99.loader/compiler_sffi.spl");
    let handle_ctx = compiler_root.join("99.loader/loader/compiler_sffi.spl");
    let consumer = compiler_root.join("70.backend/linker/obj_taker.spl");

    std::fs::write(&alive_ctx, "class CompilerContext:\n    alive: bool\n").unwrap();
    std::fs::write(&handle_ctx, "struct CompilerContext:\n    handle: i64\n").unwrap();
    std::fs::write(
        &consumer,
        "struct ObjTaker:\n    compiler_ctx: CompilerContext\n\nfn handle_of(t: ObjTaker) -> i64:\n    return t.compiler_ctx.handle\n",
    )
    .unwrap();

    let file_sources = vec![
        (alive_ctx.clone(), std::fs::read_to_string(&alive_ctx).unwrap()),
        (handle_ctx.clone(), std::fs::read_to_string(&handle_ctx).unwrap()),
        (consumer.clone(), std::fs::read_to_string(&consumer).unwrap()),
    ];
    let result = super::imports::build_import_map(&file_sources, std::slice::from_ref(&compiler_root), &src_root);

    let compiler_context_variants = result
        .duplicate_struct_defs
        .get("CompilerContext")
        .expect("expected duplicate CompilerContext layouts");
    assert!(compiler_context_variants
        .iter()
        .any(|fields| fields == &vec![("handle".to_string(), simple_parser::Type::Simple("i64".to_string()))]));

    let mut field_indices: std::collections::HashMap<String, std::collections::HashSet<usize>> =
        std::collections::HashMap::new();
    for fields in result.struct_defs.values() {
        for (idx, (field_name, _)) in fields.iter().enumerate() {
            field_indices.entry(field_name.clone()).or_default().insert(idx);
        }
    }
    let ambiguous: std::collections::HashSet<String> = field_indices
        .into_iter()
        .filter_map(|(name, indices)| if indices.len() > 1 { Some(name) } else { None })
        .collect();

    let ast = simple_parser::Parser::new(&std::fs::read_to_string(&consumer).unwrap())
        .parse()
        .unwrap();
    let mut lowerer = crate::hir::Lowerer::new();
    lowerer.set_global_struct_defs(std::sync::Arc::new(result.struct_defs));
    lowerer.set_duplicate_global_struct_defs(std::sync::Arc::new(result.duplicate_struct_defs));
    lowerer.set_ambiguous_field_names(std::sync::Arc::new(ambiguous));

    let lowered = lowerer.lower_module(&ast).unwrap();
    let func = &lowered.functions[0];
    let crate::hir::HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("expected return statement");
    };
    assert!(matches!(expr.kind, crate::hir::HirExprKind::FieldAccess { .. }));
    assert_eq!(expr.ty, crate::hir::TypeId::I64);
}

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
#[test]
fn test_runtime_retention_symbols_leave_strong_references_to_section_gc() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let runtime_c = temp.path().join("runtime.c");
    let app_c = temp.path().join("app.c");
    let runtime_o = temp.path().join("runtime.o");
    let runtime_a = temp.path().join("runtime.a");
    let app_o = temp.path().join("app.o");
    let linked = temp.path().join("app");

    std::fs::write(
        &runtime_c,
        r#"
void rt_used(void) {}
void rt_dead(void) {}
void rt_unused(void) {}
void __simple_runtime_init(void) {}
void __simple_runtime_shutdown(void) {}
void rt_set_args(void) {}
void rt_function_not_found(void) {}
void rt_string_new(void) {}
void rt_string_data(void) {}
void rt_string_len(void) {}
void rt_string_bytes(void) {}
void rt_array_new(void) {}
void rt_array_len(void) {}
void rt_declared_only(void) {}
void rt_security_load_registry_sdn(void) {}
"#,
    )
    .unwrap();
    std::fs::write(
        &app_c,
        r#"
extern void rt_used(void);
extern void rt_dead(void);
__asm__(".weak rt_declared_only");
void app_call(void) { rt_used(); }
void dead_call(void) { rt_dead(); }
int main(void) { app_call(); return 0; }
"#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&runtime_c)
        .arg("-o")
        .arg(&runtime_o)
        .status()
        .unwrap()
        .success());
    let tool = find_archive_tool();
    assert!(
        archive_create_command(&tool, &runtime_a, std::slice::from_ref(&runtime_o), false, false)
            .status()
            .unwrap()
            .success()
    );
    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&app_c)
        .arg("-o")
        .arg(&app_o)
        .status()
        .unwrap()
        .success());

    let mut all_mangled = std::collections::HashMap::new();
    all_mangled.insert("unused".to_string(), vec!["rt_unused".to_string()]);
    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(all_mangled),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let roots = NativeProjectBuilder::runtime_retention_symbols(
        std::slice::from_ref(&app_o),
        &app_o,
        None,
        &runtime_a,
        &imports,
    )
    .unwrap();

    assert!(!roots.contains(&"rt_used".to_string()));
    assert!(!roots.contains(&"rt_dead".to_string()));
    assert!(roots.contains(&"__simple_runtime_init".to_string()));
    assert!(roots.contains(&"rt_function_not_found".to_string()));
    assert!(roots.contains(&"rt_string_bytes".to_string()));
    assert!(!roots.contains(&"rt_unused".to_string()));
    assert!(!roots.contains(&"rt_declared_only".to_string()));
    assert!(!roots.contains(&"rt_security_load_registry_sdn".to_string()));

    let mut link = std::process::Command::new(&cc);
    link.arg(&app_o);
    NativeProjectBuilder::add_elf_undefined_roots(&mut link, &roots);
    assert!(link
        .arg(&runtime_a)
        .arg("-Wl,--gc-sections")
        .arg("-o")
        .arg(&linked)
        .status()
        .unwrap()
        .success());
    assert!(std::process::Command::new(&linked).status().unwrap().success());
    let symbols = nm_command().arg("-g").arg(&linked).output().unwrap();
    assert!(symbols.status.success());
    assert!(String::from_utf8_lossy(&symbols.stdout)
        .lines()
        .any(|line| line.split_whitespace().last() == Some("rt_string_bytes")));
    assert!(String::from_utf8_lossy(&symbols.stdout)
        .lines()
        .any(|line| line.split_whitespace().last() == Some("rt_used")));
    assert!(!String::from_utf8_lossy(&symbols.stdout)
        .lines()
        .any(|line| line.split_whitespace().last() == Some("rt_dead")));
}

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
#[test]
fn test_runtime_retention_symbols_include_weak_security_registry_loader() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let runtime_c = temp.path().join("runtime.c");
    let app_c = temp.path().join("app.c");
    let init_c = temp.path().join("security_init.c");
    let runtime_o = temp.path().join("runtime.o");
    let app_o = temp.path().join("app.o");
    let init_o = temp.path().join("security_init.o");

    std::fs::write(
        &runtime_c,
        r#"
unsigned long long rt_security_load_registry_sdn(const unsigned char* ptr, unsigned long long len) {
    return len + (ptr != 0);
}
"#,
    )
    .unwrap();
    std::fs::write(&app_c, "void app_call(void) {}\n").unwrap();
    std::fs::write(
        &init_c,
        r#"
extern unsigned long long rt_security_load_registry_sdn(const unsigned char*, unsigned long long) __attribute__((weak));
void __module_init_security_registry(void) {
    if (rt_security_load_registry_sdn) {
        rt_security_load_registry_sdn((const unsigned char*)"security", 8);
    }
}
"#,
    )
    .unwrap();

    for (src, obj) in [(&runtime_c, &runtime_o), (&app_c, &app_o), (&init_c, &init_o)] {
        assert!(std::process::Command::new(&cc)
            .args(["-c", "-ffunction-sections", "-fdata-sections"])
            .arg(src)
            .arg("-o")
            .arg(obj)
            .status()
            .unwrap()
            .success());
    }

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };
    let roots = NativeProjectBuilder::runtime_retention_symbols(
        std::slice::from_ref(&app_o),
        &app_o,
        Some(&init_o),
        &runtime_o,
        &imports,
    )
    .unwrap();

    assert!(
        roots.contains(&"rt_security_load_registry_sdn".to_string()),
        "weak security registry loader reference must retain the hosted runtime loader: {:?}",
        roots
    );
}

#[test]
fn test_compiler_rt_builtin_symbols_are_not_stub_candidates() {
    assert!(super::tools::is_compiler_rt_builtin_symbol("__adddf3"));
    assert!(super::tools::is_compiler_rt_builtin_symbol("__fixunsdfdi"));
    assert!(super::tools::is_compiler_rt_builtin_symbol("__muldi3"));
    assert!(!super::tools::is_compiler_rt_builtin_symbol(
        "examples__simple_os___start"
    ));
}

#[test]
fn test_cxx_abi_symbols_are_not_stub_candidates() {
    assert!(super::tools::is_system_symbol("__Znwm"));
    assert!(super::tools::is_system_symbol("_Znwm"));
    assert!(super::tools::is_system_symbol("__ZN4llvm2cl6OptionE"));
    assert!(super::tools::is_system_symbol("_GLOBAL_OFFSET_TABLE_"));
    assert!(super::tools::is_system_symbol("__tls_get_addr"));
    assert!(super::tools::is_system_symbol("_Unwind_Resume"));
    assert!(super::tools::is_system_symbol("cfsetispeed@GLIBC_2.2.5"));
    assert!(super::tools::is_system_symbol("pthread_atfork"));
    assert!(super::tools::is_system_symbol("rewind"));
    assert!(super::tools::is_system_symbol("_rewind"));
    for symbol in [
        "_cfgetispeed",
        "_class_addMethod",
        "_clock_getres",
        "_fsetattrlist",
        "_getpeereid",
        "_ivar_getName",
        "_method_getImplementation",
        "_protocol_getName",
        "_recvmsg",
        "_sendfile",
        "_setattrlist",
        "_sigaltstack",
        "_socketpair",
    ] {
        assert!(super::tools::is_system_symbol(symbol), "{symbol}");
    }
    assert!(!super::tools::is_system_symbol("app__mcp__main"));
}

#[test]
fn test_versioned_termios_symbols_are_not_stub_candidates() {
    for symbol in [
        "cfgetispeed@GLIBC_2.2.5",
        "cfgetospeed@GLIBC_2.2.5",
        "cfsetispeed@GLIBC_2.2.5",
        "cfsetospeed@GLIBC_2.2.5",
        "cfsetspeed@GLIBC_2.2.5",
    ] {
        assert!(super::tools::is_system_symbol(symbol), "{symbol}");
    }
}

#[cfg(not(target_os = "windows"))]
#[test]
fn test_generate_stub_object_skips_optional_weak_entry_hooks() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let main_c = temp.path().join("main.c");
    let main_o = temp.path().join("main.o");

    std::fs::write(
        &main_c,
        r#"
extern int __attribute__((weak)) spl_main(void);
extern void __attribute__((weak)) rt_set_args(int argc, char** argv);
extern void __attribute__((weak)) __simple_runtime_init(void);
extern void __attribute__((weak)) __simple_runtime_shutdown(void);
extern void __attribute__((weak)) __simple_call_module_inits(void);

int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (__simple_call_module_inits) __simple_call_module_inits();
    if (rt_set_args) rt_set_args(argc, argv);
    return spl_main ? spl_main() : 0;
}
"#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&main_c)
        .arg("-o")
        .arg(&main_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let stub_o = super::stubs::generate_stub_object(temp.path(), &[], &main_o, &[], &imports).unwrap();
    let output = std::process::Command::new("nm")
        .arg("-g")
        .arg(&stub_o)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("spl_main"));
    assert!(!stdout.contains("rt_set_args"));
    assert!(!stdout.contains("__simple_runtime_init"));
    assert!(!stdout.contains("__simple_runtime_shutdown"));
    assert!(!stdout.contains("__simple_call_module_inits"));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn empty_module_init_set_still_emits_main_stub_owner() {
    let temp = tempfile::tempdir().unwrap();
    let output = temp.path().join("probe");
    let builder = NativeProjectBuilder::new(temp.path().to_path_buf(), output);

    let init_object = builder
        .generate_init_caller(temp.path(), &[], None)
        .unwrap()
        .expect("empty init set must still own __simple_call_module_inits");
    let symbols = std::process::Command::new("nm")
        .arg("-g")
        .arg(&init_object)
        .output()
        .unwrap();
    assert!(symbols.status.success());
    assert!(String::from_utf8_lossy(&symbols.stdout).contains("__simple_call_module_inits"));

    let main_object = builder.compile_main_stub(temp.path()).unwrap();
    let linked_probe = temp.path().join("linked-probe");
    let link_status = std::process::Command::new("c++")
        .arg(&main_object)
        .arg(&init_object)
        .arg("-o")
        .arg(&linked_probe)
        .status()
        .unwrap();
    assert!(
        link_status.success(),
        "optional main-stub hooks must link without providers"
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn test_bootstrap_stub_mode_defers_libc_process_symbols_to_linker() {
    let _guard = no_stub_fallback_env_lock().lock().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let previous = std::env::var("SIMPLE_STUB_MISSING_RT").ok();
    std::env::set_var("SIMPLE_STUB_MISSING_RT", "1");

    let temp = tempfile::tempdir().unwrap();
    let main_c = temp.path().join("main.c");
    let main_o = temp.path().join("main.o");

    std::fs::write(
        &main_c,
        r#"
#include <stdio.h>
int main(void) {
    FILE* f = popen("printf 2", "r");
    if (!f) return 1;
    char buf[8];
    char* got = fgets(buf, sizeof(buf), f);
    return got ? pclose(f) : 1;
}
"#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&main_c)
        .arg("-o")
        .arg(&main_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let stub_o = super::stubs::generate_stub_object(temp.path(), &[], &main_o, &[], &imports).unwrap();

    match previous.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_STUB_MISSING_RT", value),
        None => std::env::remove_var("SIMPLE_STUB_MISSING_RT"),
    }

    let output = std::process::Command::new("nm").arg("-g").arg(stub_o).output().unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("popen"));
    assert!(!stdout.contains("fgets"));
    assert!(!stdout.contains("pclose"));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn test_no_stub_fallback_defers_unresolved_host_symbols_to_linker() {
    let _guard = no_stub_fallback_env_lock().lock().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let previous = std::env::var("SIMPLE_NO_STUB_FALLBACK").ok();
    std::env::set_var("SIMPLE_NO_STUB_FALLBACK", "1");

    let temp = tempfile::tempdir().unwrap();
    let main_c = temp.path().join("main.c");
    let main_o = temp.path().join("main.o");

    std::fs::write(
        &main_c,
        r#"
extern long missing_simple_symbol(void);
int main(void) {
    return (int)missing_simple_symbol();
}
"#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&main_c)
        .arg("-o")
        .arg(&main_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let stub_o = super::stubs::generate_stub_object(temp.path(), &[], &main_o, &[], &imports).unwrap();

    match previous.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_NO_STUB_FALLBACK", value),
        None => std::env::remove_var("SIMPLE_NO_STUB_FALLBACK"),
    }

    let output = std::process::Command::new("nm").arg("-g").arg(stub_o).output().unwrap();
    assert!(output.status.success());
    assert!(!String::from_utf8_lossy(&output.stdout).contains("missing_simple_symbol"));
}

#[cfg(not(target_os = "windows"))]
#[test]
fn test_no_stub_fallback_keeps_resolved_simple_aliases() {
    let _guard = no_stub_fallback_env_lock().lock().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let previous = std::env::var("SIMPLE_NO_STUB_FALLBACK").ok();
    std::env::set_var("SIMPLE_NO_STUB_FALLBACK", "1");

    let temp = tempfile::tempdir().unwrap();
    let main_c = temp.path().join("main.c");
    let main_o = temp.path().join("main.o");
    std::fs::write(
        &main_c,
        r#"
extern long run_check(void);
long cli__check__run_check(void) { return 7; }
int main(void) { return (int)run_check(); }
"#,
    )
    .unwrap();
    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&main_c)
        .arg("-o")
        .arg(&main_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };
    let stub_o = super::stubs::generate_stub_object(temp.path(), &[], &main_o, &[], &imports).unwrap();

    match previous.as_deref() {
        Some(value) => std::env::set_var("SIMPLE_NO_STUB_FALLBACK", value),
        None => std::env::remove_var("SIMPLE_NO_STUB_FALLBACK"),
    }

    let output = std::process::Command::new("nm").arg("-g").arg(stub_o).output().unwrap();
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("run_check"));
}

#[cfg(target_os = "linux")]
#[test]
fn test_core_c_lane_builds_and_runs_hello_world_small() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let output_dir = PathBuf::from("/tmp/simple-core-c-regression");
    let _ = std::fs::create_dir_all(&output_dir);
    let output = output_dir.join("hello_simple");

    let result = NativeProjectBuilder::new(repo_root.clone(), output.clone())
        .config(NativeBuildConfig {
            entry_closure: true,
            runtime_bundle: "core-c".to_string(),
            strip: true,
            incremental: false,
            ..NativeBuildConfig::default()
        })
        .source_dir(repo_root.join("src/lib"))
        .source_dir(repo_root.join("src/app"))
        .entry_file(repo_root.join("examples/01_getting_started/hello_native.spl"))
        .build()
        .unwrap();

    assert!(result.binary_size < 128_000, "hello too large: {}", result.binary_size);

    let run = std::process::Command::new(&output).output().unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert!(
            run.status.success(),
            "hello exit: code={:?} signal={:?} stdout=`{}` stderr=`{}` path={}",
            run.status.code(),
            run.status.signal(),
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr),
            output.display()
        );
    }
    #[cfg(not(unix))]
    {
        assert!(
            run.status.success(),
            "hello exit: code={:?} stdout=`{}` stderr=`{}` path={}",
            run.status.code(),
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr),
            output.display()
        );
    }
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "Hello World");
}

#[cfg(target_os = "linux")]
#[test]
fn test_native_project_emit_archive_writes_static_archive() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();
    let module = source_dir.join("runtime_piece.spl");
    std::fs::write(
        &module,
        r#"
fn simple_core_archive_probe() -> i64:
    return 42

fn rt_simple_core_archive_probe() -> i64:
    return 7

fn __simple_core_archive_probe() -> i64:
    return 9

fn plain_archive_param_probe(value: i64) -> i64:
    return value + 1

fn rt_archive_param_probe(value: i64) -> i64:
    return value + 2

fn rt_value_int(value: i64) -> i64:
    return value << 3

security gate ArchiveSecurityGate:
    from feature user
    to feature admin
    policy ArchivePolicy
    audit all
    sandbox archive_sandbox

sandbox archive_sandbox:
    backend auto
"#,
    )
    .unwrap();

    let archive = temp.path().join("libsimple_runtime.a");
    let result = NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(NativeBuildConfig {
            emit_archive: true,
            clean: true,
            incremental: false,
            no_mangle: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(source_dir)
        .build()
        .unwrap();

    assert_eq!(result.output, archive);
    assert!(archive.exists());
    assert!(std::fs::metadata(&archive).unwrap().len() > 0);

    let symbols = std::process::Command::new("nm")
        .arg("-g")
        .arg("--defined-only")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(symbols.status.success());
    let stdout = String::from_utf8_lossy(&symbols.stdout);
    assert!(
        stdout.contains("simple_core_archive_probe"),
        "archive symbols did not include probe function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("rt_simple_core_archive_probe"),
        "archive symbols did not include runtime-style probe function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("__simple_core_archive_probe"),
        "archive symbols did not include __simple-style probe function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("plain_archive_param_probe"),
        "archive symbols did not include plain parameterized probe function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("rt_archive_param_probe"),
        "archive symbols did not include runtime-style parameterized probe function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("rt_value_int"),
        "archive symbols did not include known runtime-SFFI parameterized function:\n{}",
        stdout
    );
    assert!(
        stdout.contains("__module_init_security_registry"),
        "archive symbols did not include generated security registry module init:\n{}",
        stdout
    );
    assert!(
        stdout.contains("__simple_call_module_inits"),
        "archive symbols did not include generated module-init caller:\n{}",
        stdout
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_simple_runtime_memory_intrinsics_lower_without_helper_symbols() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();
    let module = source_dir.join("memory_intrinsics.spl");
    std::fs::write(
        &module,
        r#"
extern fn spl_load_i64(ptr: i64, offset: i64) -> i64
extern fn spl_store_i64(ptr: i64, offset: i64, value: i64)
extern fn spl_load_u8(ptr: i64, offset: i64) -> i64
extern fn spl_store_u8(ptr: i64, offset: i64, value: i64)

fn probe_store_i64(ptr: i64, offset: i64, value: i64):
    spl_store_i64(ptr, offset, value)

fn probe_load_i64(ptr: i64, offset: i64) -> i64:
    return spl_load_i64(ptr, offset)

fn probe_store_u8(ptr: i64, offset: i64, value: i64):
    spl_store_u8(ptr, offset, value)

fn probe_load_u8(ptr: i64, offset: i64) -> i64:
    return spl_load_u8(ptr, offset)
"#,
    )
    .unwrap();

    let archive = temp.path().join("libsimple_runtime.a");
    let result = NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(NativeBuildConfig {
            emit_archive: true,
            clean: true,
            incremental: false,
            no_mangle: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(source_dir)
        .build()
        .unwrap();

    assert_eq!(result.output, archive);
    assert!(archive.exists());

    let symbols = std::process::Command::new("nm")
        .arg("-u")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(symbols.status.success());
    let undefineds = String::from_utf8_lossy(&symbols.stdout);
    for helper in ["spl_load_i64", "spl_store_i64", "spl_load_u8", "spl_store_u8"] {
        assert!(
            !undefineds.contains(helper),
            "memory intrinsic {helper} leaked as undefined helper symbol:\n{undefineds}"
        );
    }

    let probe_source = temp.path().join("memory_intrinsics_probe.c");
    let probe_exe = temp.path().join("memory_intrinsics_probe");
    std::fs::write(
        &probe_source,
        r#"
#include <stdint.h>

void probe_store_i64(int64_t ptr, int64_t offset, int64_t value);
int64_t probe_load_i64(int64_t ptr, int64_t offset);
void probe_store_u8(int64_t ptr, int64_t offset, int64_t value);
int64_t probe_load_u8(int64_t ptr, int64_t offset);

int main(void) {
    uint8_t bytes[24] = {0};
    probe_store_i64((int64_t)(uintptr_t)bytes, 8, 0x1122334455667788LL);
    if (probe_load_i64((int64_t)(uintptr_t)bytes, 8) != 0x1122334455667788LL) return 10;
    probe_store_u8((int64_t)(uintptr_t)bytes, 3, 0xab);
    if (probe_load_u8((int64_t)(uintptr_t)bytes, 3) != 0xab) return 11;
    return 0;
}
"#,
    )
    .unwrap();
    let status = std::process::Command::new(find_c_compiler())
        .arg(&probe_source)
        .arg(&archive)
        .arg("-o")
        .arg(&probe_exe)
        .status()
        .unwrap();
    assert!(status.success(), "failed to compile Simple memory intrinsic probe");
    let output = std::process::Command::new(&probe_exe).output().unwrap();
    assert!(
        output.status.success(),
        "Simple memory intrinsic probe failed: code={:?} stdout=`{}` stderr=`{}`",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_simple_core_enum_registry_rejects_raw_tag_collisions() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("libsimple_runtime.a");

    NativeProjectBuilder::new(repo_root.clone(), archive.clone())
        .config(NativeBuildConfig {
            emit_archive: true,
            clean: true,
            incremental: false,
            no_mangle: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(repo_root.join("src/runtime/simple_core"))
        .build()
        .unwrap();

    let probe_source = temp.path().join("simple_core_enum_registry_probe.c");
    let probe_exe = temp.path().join("simple_core_enum_registry_probe");
    std::fs::write(
        &probe_source,
        r#"
#include <stdint.h>

int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);
int64_t rt_enum_id(int64_t value);
int8_t rt_is_none(int64_t value);

int main(void) {
    if (rt_enum_id(4097) != -1 || rt_enum_id(-7) != -1) return 1;
    if (rt_is_none(4097) || rt_is_none(-7)) return 2;
    int64_t none = rt_enum_new(1, 1, 3);
    if (rt_enum_id(none) != 1 || !rt_is_none(none)) return 3;
    return 0;
}
"#,
    )
    .unwrap();
    let status = std::process::Command::new(find_c_compiler())
        .arg(&probe_source)
        .arg(&archive)
        .arg("-o")
        .arg(&probe_exe)
        .status()
        .unwrap();
    assert!(status.success(), "failed to compile pure-Simple enum registry probe");
    let output = std::process::Command::new(&probe_exe).output().unwrap();
    assert!(
        output.status.success(),
        "pure-Simple enum registry probe failed: code={:?} stdout=`{}` stderr=`{}`",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_simple_core_source_tree_emits_partial_runtime_archive() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let source_dir = repo_root.join("src/runtime/simple_core");
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("libsimple_runtime.a");

    let result = NativeProjectBuilder::new(repo_root.clone(), archive.clone())
        .config(NativeBuildConfig {
            emit_archive: true,
            clean: true,
            incremental: false,
            no_mangle: true,
            ..NativeBuildConfig::default()
        })
        .source_dir(source_dir)
        .build()
        .unwrap();

    assert_eq!(result.output, archive);
    assert!(archive.exists());
    let symbols = std::process::Command::new("nm")
        .arg("-g")
        .arg("--defined-only")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(symbols.status.success());
    let stdout = String::from_utf8_lossy(&symbols.stdout);
    let missing = simple_common::CORE_REQUIRED_RUNTIME_SYMBOLS
        .iter()
        .filter(|symbol| {
            !stdout
                .lines()
                .any(|line| line.split_whitespace().last() == Some(**symbol))
        })
        .copied()
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty() && runtime_archive_has_core_required_symbols(&archive),
        "pure-Simple source tree missing core-required symbols: {missing:?}"
    );
    for symbol in [
        "__simple_runtime_init",
        "__simple_runtime_shutdown",
        "rt_value_int",
        "rt_value_as_int",
        "rt_pool_safepoint",
        "rt_value_float",
        "rt_value_bool",
        "rt_value_nil",
        "rt_alloc",
        "rt_realloc",
        "rt_free",
        "rt_memcpy",
        "rt_memset",
        "rt_exit",
        "rt_time_now_unix",
        "rt_sleep_ms",
        "rt_panic",
        "rt_stdout_flush",
        "rt_stderr_flush",
        "rt_array_new",
        "rt_array_new_with_cap_u64",
        "rt_array_len",
        "rt_array_get",
        "rt_array_set",
        "rt_array_push",
        "rt_array_pop",
        "rt_for_iterable",
        "rt_typed_words_u64_data_at_checked",
        "rt_typed_words_u64_raw_data_at",
        "rt_typed_words_u64_store_known_data_at",
        "rt_string_new",
        "rt_string_len",
        "rt_string_data",
        "rt_string_bytes",
        "rt_string_char_code_at",
        "rt_any_add",
        "rt_string_concat",
        "rt_len",
        "rt_native_eq",
        "rt_native_neq",
        "rt_slice",
        "rt_string_starts_with",
        "rt_string_ends_with",
        "rt_string_trim",
        "rt_string_to_int",
        "rt_string_replace",
        "rt_to_string",
        "rt_stdout_write",
        "rt_stderr_write",
        "stdin_read_char",
        "print_raw",
    ] {
        assert!(
            stdout.contains(symbol),
            "pure-Simple runtime archive missing {symbol}:\n{stdout}"
        );
    }

    let probe_source = temp.path().join("simple_core_value_memory_probe.c");
    let probe_exe = temp.path().join("simple_core_value_memory_probe");
    std::fs::write(
        &probe_source,
        r#"
#include <stdint.h>
#include <string.h>
#include "runtime.h"

int main(void) {
    extern int64_t rt_value_as_int(int64_t);
    extern int64_t rt_string_bytes(int64_t);
    extern int64_t rt_string_char_code_at(int64_t, int64_t);
    extern int64_t rt_any_add(int64_t, int64_t);
    extern int64_t rt_for_iterable(int64_t);
    extern int64_t rt_index_get(int64_t, int64_t);
    extern int8_t rt_index_set(int64_t, int64_t, int64_t);
    extern int64_t rt_pool_safepoint(void);
    extern int64_t rt_dict_new(int64_t);
    extern int64_t rt_dict_get(int64_t, int64_t);
    extern int8_t rt_dict_set(int64_t, int64_t, int64_t);
    extern int8_t rt_dict_contains(int64_t, int64_t);
    extern int8_t rt_dict_remove(int64_t, int64_t);
    extern int64_t rt_dict_len(int64_t);
    extern int64_t rt_dict_keys(int64_t);
    extern int64_t rt_dict_values(int64_t);
    extern int64_t rt_dict_entries(int64_t);
    extern int8_t rt_is_none(int64_t);
    extern int64_t rt_string_builder_new(void);
    extern int64_t rt_string_builder_push(int64_t, int64_t);
    extern int64_t rt_string_builder_finish(int64_t);
    extern int64_t rt_string_builder_len(int64_t);
    if (rt_value_int(7) != 56) return 10;
    if (rt_value_as_int(rt_value_int(-7)) != -7) return 15;
    if (rt_pool_safepoint() != 0) return 16;
    if (rt_for_iterable(rt_value_int(9)) != rt_value_int(9)) return 17;
    if (rt_value_as_int(rt_any_add(rt_value_int(4), rt_value_int(5))) != 9) return 18;
    if (rt_value_bool(1) != 11) return 11;
    if (rt_value_bool(0) != 19) return 12;
    if (rt_value_nil() != 3) return 13;
    if (rt_value_float(0x123456789LL) != ((0x123456789LL & ~7LL) | 2LL)) return 14;

    uint8_t* p = (uint8_t*)rt_alloc(4);
    if (!p) return 20;
    rt_memset(p, 0x5a, 4);
    if (p[0] != 0x5a || p[3] != 0x5a) return 21;
    uint8_t* q = (uint8_t*)rt_alloc(4);
    if (!q) return 22;
    rt_memset(q, 0x21, 4);
    rt_memcpy(p, q, 4);
    if (p[0] != 0x21 || p[3] != 0x21) return 23;
    p = (uint8_t*)rt_realloc(p, 8);
    if (!p || p[0] != 0x21) return 24;
    rt_free(q);
    rt_free(p);
    if (rt_time_now_unix() <= 0) return 30;
    rt_sleep_ms(0);
    rt_stdout_flush();
    rt_stderr_flush();

    SplArray* a = rt_array_new(1);
    if (!a) return 40;
    if (rt_array_len(a) != 0) return 41;
    if (!rt_array_push(a, rt_value_int(10))) return 42;
    if (!rt_array_push(a, rt_value_int(20))) return 43;
    if (rt_array_len(a) != 2) return 44;
    if (rt_array_get(a, 0) != rt_value_int(10)) return 45;
    if (rt_array_get(a, 1) != rt_value_int(20)) return 46;
    rt_array_set(a, -1, rt_value_int(30));
    if (rt_array_get(a, 1) != rt_value_int(30)) return 47;
    extern int64_t rt_array_pop(SplArray*);
    extern int64_t rt_typed_words_u64_data_at_checked(int64_t, int64_t, int64_t);
    if (rt_array_pop(a) != rt_value_int(30)) return 48;
    if (rt_array_len(a) != 1) return 49;
    if (rt_array_get(a, 99) != 3) return 50;
    SplArray* indexed = rt_array_new(10);
    if (!indexed) return 51;
    for (int64_t i = 0; i < 10; i++) {
        if (!rt_array_push(indexed, rt_value_int(i))) return 52;
    }
    if (rt_index_get((int64_t)indexed, rt_value_int(8)) != rt_value_int(8)) return 53;
    if (!rt_index_set((int64_t)indexed, rt_value_int(8), rt_value_int(80))) return 54;
    if (rt_array_get(indexed, 8) != rt_value_int(80)) return 55;
    SplArray* words = rt_array_new_with_cap_u64(2);
    if (!words) return 51;
    int64_t word_header = rt_array_header_ptr(words);
    int64_t word_data = rt_array_data_ptr(words);
    if (!rt_typed_words_u64_store_known_data_at(word_header, word_data, 0, 0x102030405060708LL)) return 52;
    if (rt_typed_words_u64_data_at_checked(word_header, word_data, 0) != 0x102030405060708LL) return 53;
    if (rt_typed_words_u64_raw_data_at(word_data, 0) != 0x102030405060708LL) return 54;
    if (rt_typed_words_u64_data_at_checked(word_header, word_data, 3) != 0) return 55;

    int64_t s = rt_string_new((const uint8_t*)" 123 ", 5);
    if (rt_string_len(s) != 5) return 60;
    if (memcmp(rt_string_data(s), " 123 ", 5) != 0) return 61;
    if (rt_len(s) != 5) return 62;
    int64_t t = rt_string_new((const uint8_t*)"abc", 3);
    SplArray* t_bytes = (SplArray*)rt_string_bytes(t);
    if (rt_array_len(t_bytes) != 3 || rt_value_as_int(rt_array_get(t_bytes, 1)) != 'b') return 77;
    if (rt_string_char_code_at(t, 2) != 'c') return 78;
    int64_t utf8 = rt_string_new((const uint8_t*)"\xC3\xA9", 2);
    if (rt_string_char_code_at(utf8, 0) != 0xE9) return 79;

    int64_t dict = rt_dict_new(1);
    if (dict == 3 || rt_dict_len(dict) != 0) return 80;
    int64_t key1 = rt_string_new((const uint8_t*)"k", 1);
    int64_t key2 = rt_string_new((const uint8_t*)"k", 1);
    if (!rt_dict_set(dict, key1, rt_value_int(1))) return 81;
    if (!rt_dict_set(dict, key2, rt_value_int(2))) return 82;
    if (rt_dict_len(dict) != 1 || rt_dict_get(dict, key1) != rt_value_int(2)) return 83;
    if (!rt_dict_set(dict, 5, rt_value_int(3))) return 84;
    if (rt_dict_get(dict, rt_value_int(5)) != rt_value_int(3)) return 85;
    int64_t key3 = rt_string_new((const uint8_t*)"z", 1);
    if (!rt_index_set(dict, key3, rt_value_int(4))) return 86;
    if (rt_index_get(dict, key3) != rt_value_int(4)) return 87;
    if (rt_array_len((SplArray*)rt_dict_keys(dict)) != 3) return 88;
    if (rt_array_len((SplArray*)rt_dict_values(dict)) != 3) return 89;
    int64_t entries = rt_dict_entries(dict);
    if (rt_array_len((SplArray*)entries) != 3) return 90;
    if (rt_array_len((SplArray*)rt_array_get((SplArray*)entries, 0)) != 2) return 91;
    if (!rt_dict_contains(dict, key3) || !rt_dict_remove(dict, key3)) return 92;
    if (rt_dict_contains(dict, key3) || rt_dict_get(dict, key3) != 3) return 93;

    int64_t none = rt_enum_new(1, 1, 3);
    int64_t some = rt_enum_new(1, 0, rt_value_int(9));
    if (rt_enum_id(none) != 1 || rt_enum_id(some) != 1 || rt_enum_id(rt_value_int(9)) != -1) return 104;
    if (rt_enum_id(4097) != -1 || rt_enum_id(-7) != -1) return 105;
    if (rt_is_none(4097) || rt_is_none(-7)) return 106;
    if (!rt_is_none(none) || rt_is_some(none)) return 94;
    if (rt_is_none(some) || !rt_is_some(some)) return 95;
    if (rt_enum_discriminant(some) != 0) return 96;
    if (!rt_enum_check_discriminant(some, 0)) return 97;
    if (rt_enum_payload(some) != rt_value_int(9)) return 98;
    if (rt_unwrap_or_self(some) != rt_value_int(9)) return 99;
    if (rt_unwrap_or_self(rt_value_int(9)) != rt_value_int(9)) return 100;
    int64_t builder = rt_string_builder_new();
    if (!builder || !rt_string_builder_push(builder, t) ||
        !rt_string_builder_push(builder, rt_string_new((const uint8_t*)"def", 3))) return 101;
    if (rt_string_builder_len(builder) != 6) return 102;
    int64_t built = rt_string_builder_finish(builder);
    if (rt_string_len(built) != 6 || memcmp(rt_string_data(built), "abcdef", 6) != 0) return 103;
    int64_t u = rt_string_new((const uint8_t*)"def", 3);
    int64_t c = rt_string_concat(t, u);
    if (rt_string_len(c) != 6 || memcmp(rt_string_data(c), "abcdef", 6) != 0) return 63;
    if (!rt_string_starts_with(c, t)) return 64;
    if (!rt_string_ends_with(c, u)) return 65;
    if (!rt_native_eq(t, rt_string_new((const uint8_t*)"abc", 3))) return 66;
    if (!rt_native_neq(t, u)) return 67;
    int64_t sliced = rt_slice(c, 1, 4, 1);
    if (rt_string_len(sliced) != 3 || memcmp(rt_string_data(sliced), "bcd", 3) != 0) return 68;
    int64_t trimmed = rt_string_trim(s);
    if (rt_string_len(trimmed) != 3 || memcmp(rt_string_data(trimmed), "123", 3) != 0) return 69;
    if (rt_string_to_int(trimmed) != 123) return 70;
    int64_t replaced = rt_string_replace(c, rt_string_new((const uint8_t*)"cd", 2), rt_string_new((const uint8_t*)"XY", 2));
    if (rt_string_len(replaced) != 6 || memcmp(rt_string_data(replaced), "abXYef", 6) != 0) return 71;
    int64_t int_text = rt_to_string(rt_value_int(42));
    if (rt_string_len(int_text) != 2 || memcmp(rt_string_data(int_text), "42", 2) != 0) return 72;
    int64_t true_text = rt_to_string(rt_value_bool(1));
    if (rt_string_len(true_text) != 4 || memcmp(rt_string_data(true_text), "true", 4) != 0) return 73;
    if (rt_stdout_write(rt_string_new(NULL, 0)) != 0) return 74;
    if (rt_stderr_write(rt_string_new(NULL, 0)) != 0) return 75;
    if (print_raw(rt_string_new(NULL, 0)) != 0) return 76;
    return 0;
}
"#,
    )
    .unwrap();
    let status = std::process::Command::new(find_c_compiler())
        .arg("-I")
        .arg(repo_root.join("src/runtime"))
        .arg(&probe_source)
        .arg(&archive)
        .arg("-o")
        .arg(&probe_exe)
        .status()
        .unwrap();
    assert!(status.success(), "failed to compile pure-Simple value/memory probe");
    let output = std::process::Command::new(&probe_exe).output().unwrap();
    assert!(
        output.status.success(),
        "pure-Simple value/memory probe failed: code={:?} stdout=`{}` stderr=`{}`",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[cfg(target_os = "linux")]
#[test]
fn test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest_dir
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
    let output_dir = PathBuf::from("/tmp/simple-lsp-mcp-core-c-startup");
    let _ = std::fs::create_dir_all(&output_dir);
    let output = output_dir.join("simple_lsp_mcp_startup");

    let result = NativeProjectBuilder::new(repo_root.clone(), output.clone())
        .config(NativeBuildConfig {
            entry_closure: true,
            runtime_bundle: "core-c".to_string(),
            strip: true,
            incremental: false,
            ..NativeBuildConfig::default()
        })
        .source_dir(repo_root.join("src/app"))
        .source_dir(repo_root.join("src/lib"))
        .entry_file(repo_root.join("src/app/simple_lsp_mcp/main.spl"))
        .build()
        .unwrap();

    assert!(
        result.binary_size < 512_000,
        "startup-only simple_lsp_mcp too large: {}",
        result.binary_size
    );

    let request = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}";
    let framed = format!("Content-Length: {}\r\n\r\n{}", request.len(), request);
    let mut child = std::process::Command::new(&output)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    {
        use std::io::Write;
        child.stdin.as_mut().unwrap().write_all(framed.as_bytes()).unwrap();
    }
    let run = child.wait_with_output().unwrap();
    assert!(
        run.status.success(),
        "simple_lsp_mcp startup exit: code={:?} stdout=`{}` stderr=`{}`",
        run.status.code(),
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.starts_with("Content-Length: "),
        "missing framed response: `{}`",
        stdout
    );
    assert!(
        stdout.contains("\"id\":1"),
        "missing request id in response: `{}`",
        stdout
    );
    assert!(
        stdout.contains("\"serverInfo\":{\"name\":\"simple-lsp-mcp\""),
        "missing serverInfo in response: `{}`",
        stdout
    );
}

#[test]
fn test_freestanding_weak_boot_alias_uses_strong_simple_suffix_match() {
    let temp = tempfile::tempdir().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let boot_c = temp.path().join("boot.c");
    let simple_c = temp.path().join("simple.c");
    let boot_o = temp.path().join("boot.o");
    let simple_o = temp.path().join("simple.o");

    std::fs::write(
        &boot_c,
        r#"
        __attribute__((weak)) long spl_handle_enter_user_blocking(unsigned long a0, unsigned long a1, unsigned long a2, unsigned long a3, unsigned long a4, unsigned long a5) {
            (void)a0; (void)a1; (void)a2; (void)a3; (void)a4; (void)a5;
            return -38;
        }
        "#,
    )
    .unwrap();
    std::fs::write(
        &simple_c,
        r#"
        long kernel__abi__syscall_shim__spl_handle_enter_user_blocking(unsigned long a0, unsigned long a1, unsigned long a2, unsigned long a3, unsigned long a4, unsigned long a5) {
            (void)a0; (void)a1; (void)a2; (void)a3; (void)a4; (void)a5;
            return 14;
        }
        "#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&boot_c)
        .arg("-o")
        .arg(&boot_o)
        .status()
        .unwrap()
        .success());
    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&simple_c)
        .arg("-o")
        .arg(&simple_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        trait_impls: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        data_types: std::sync::Arc::new(std::collections::HashMap::new()),
        package_data: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_arities: std::sync::Arc::new(std::collections::HashMap::new()),
        fn_return_types: std::sync::Arc::new(std::collections::HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let aliases = NativeProjectBuilder::freestanding_weak_boot_defsyms(&[simple_o], &[boot_o], &imports).unwrap();

    assert_eq!(
        aliases,
        vec![(
            "spl_handle_enter_user_blocking".to_string(),
            "kernel__abi__syscall_shim__spl_handle_enter_user_blocking".to_string()
        )]
    );
}

#[test]
fn test_freestanding_qualified_to_bare_alias_bridges_export_symbol() {
    // Mirror the rv64 kernel failure: a caller object references the fully
    // module-qualified `os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind`,
    // while the defining object emits the bare C-ABI symbol `rt_io_tcp_bind`
    // (because the function carries `@export`). The bridge must alias the
    // qualified reference onto the bare definition.
    let temp = tempfile::tempdir().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let def_c = temp.path().join("def.c");
    let caller_c = temp.path().join("caller.c");
    let def_o = temp.path().join("def.o");
    let caller_o = temp.path().join("caller.o");

    // Definition object: emits the bare exported symbol only.
    std::fs::write(
        &def_c,
        r#"
        long rt_io_tcp_bind(long addr) { return addr + 1; }
        "#,
    )
    .unwrap();
    // Caller object: references the fully module-qualified name (undefined here).
    std::fs::write(
        &caller_c,
        r#"
        extern long os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind(long addr);
        long caller_use(long x) { return os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind(x); }
        "#,
    )
    .unwrap();

    for (src, obj) in [(&def_c, &def_o), (&caller_c, &caller_o)] {
        assert!(std::process::Command::new(&cc)
            .args(["-c", "-ffunction-sections", "-fdata-sections"])
            .arg(src)
            .arg("-o")
            .arg(obj)
            .status()
            .unwrap()
            .success());
    }

    let aliases = NativeProjectBuilder::freestanding_qualified_to_bare_defsyms(&[def_o, caller_o], &[]).unwrap();

    assert_eq!(
        aliases,
        vec![(
            "os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind".to_string(),
            "rt_io_tcp_bind".to_string()
        )]
    );
}

#[test]
fn test_freestanding_spl_main_is_entry_fallback() {
    let temp = tempfile::tempdir().unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let main_c = temp.path().join("main.c");
    let main_o = temp.path().join("main.o");

    std::fs::write(
        &main_c,
        r#"
        int spl_main(void) { return 7; }
        "#,
    )
    .unwrap();

    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&main_c)
        .arg("-o")
        .arg(&main_o)
        .status()
        .unwrap()
        .success());

    let mut symbol_cache = std::collections::HashMap::new();
    let entry = NativeProjectBuilder::freestanding_simple_main_entry_symbol(&[main_o], &mut symbol_cache).unwrap();

    assert_eq!(entry, Some("spl_main".to_string()));
}

/// A failed module must abort before cached objects can be linked into a
/// successful-looking output.
#[cfg(target_os = "linux")]
#[test]
fn test_compile_failure_does_not_link_cached_objects() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();

    std::fs::write(
        source_dir.join("cached.spl"),
        "fn cached_probe() -> i64:\n    return 101\n",
    )
    .unwrap();
    let failing = source_dir.join("failing.spl");
    std::fs::write(&failing, "fn failing_probe() -> i64:\n    return 202\n").unwrap();

    let cache_dir = temp.path().join(".simple_native_cache_fail_closed");
    let archive = temp.path().join("libfail_closed.a");
    let config = || NativeBuildConfig {
        emit_archive: true,
        incremental: true,
        parallel: false,
        no_mangle: true,
        cache_dir: Some(cache_dir.clone()),
        ..NativeBuildConfig::default()
    };

    NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(config())
        .source_dir(source_dir.clone())
        .build()
        .unwrap();
    assert!(cache_dir.join("objects").is_dir());

    std::fs::remove_file(&archive).unwrap();
    std::fs::write(&failing, "fn failing_probe() -> i64:\n    return )\n").unwrap();

    let error = NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(config())
        .source_dir(source_dir)
        .build()
        .unwrap_err();

    assert!(error.contains("native-build aborted: 1 file(s) failed to compile"));
    assert!(error.contains("failing.spl"));
    assert!(!archive.exists(), "cached objects were linked after a module failed");
}

/// Regression test for a suspected cache hit/miss mix bug (issue #64): when an
/// incremental native-project build has some modules served from the object
/// cache and others freshly compiled (because only one module's source
/// changed between builds), every module's object must still make it into
/// the final link set. Builds a 2-module project twice with the same cache
/// dir, touching only `module_b.spl` between builds (forcing `module_a.spl`
/// to be a cache hit on the second build and `module_b.spl` a cache miss),
/// then asserts both modules' symbols are present in the linked archive.
#[cfg(target_os = "linux")]
#[test]
fn test_incremental_cache_hit_miss_mix_preserves_all_link_inputs() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();

    let module_a = source_dir.join("module_a.spl");
    std::fs::write(
        &module_a,
        r#"
fn cache_mix_probe_a() -> i64:
    return 101
"#,
    )
    .unwrap();

    let module_b = source_dir.join("module_b.spl");
    std::fs::write(
        &module_b,
        r#"
fn cache_mix_probe_b() -> i64:
    return 202
"#,
    )
    .unwrap();

    let cache_dir = temp.path().join(".simple_native_cache");
    let archive = temp.path().join("libcache_mix.a");

    let make_config = || NativeBuildConfig {
        emit_archive: true,
        incremental: true,
        clean: false,
        no_mangle: true,
        cache_dir: Some(cache_dir.clone()),
        ..NativeBuildConfig::default()
    };

    // Build 1: both modules are cache misses (cache dir is fresh).
    let result1 = NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(make_config())
        .source_dir(source_dir.clone())
        .build()
        .unwrap();
    assert_eq!(result1.output, archive);
    assert!(archive.exists(), "build 1 did not produce an archive");

    fn archive_symbols(archive: &Path) -> String {
        let symbols = std::process::Command::new("nm")
            .arg("-g")
            .arg("--defined-only")
            .arg(archive)
            .output()
            .unwrap();
        assert!(symbols.status.success(), "nm failed on {}", archive.display());
        String::from_utf8_lossy(&symbols.stdout).to_string()
    }

    let stdout1 = archive_symbols(&archive);
    assert!(
        stdout1.contains("cache_mix_probe_a"),
        "build 1 missing probe_a:\n{}",
        stdout1
    );
    assert!(
        stdout1.contains("cache_mix_probe_b"),
        "build 1 missing probe_b:\n{}",
        stdout1
    );

    // Touch only module_b so build 2 sees module_a as a cache HIT and
    // module_b as a cache MISS -- the hit/miss mix this test targets.
    std::fs::write(
        &module_b,
        r#"
fn cache_mix_probe_b() -> i64:
    return 303
"#,
    )
    .unwrap();

    // Build 2: reuse the same cache dir and output path.
    let result2 = NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(make_config())
        .source_dir(source_dir.clone())
        .build()
        .unwrap();
    assert_eq!(result2.output, archive);
    assert!(archive.exists(), "build 2 did not produce an archive");

    let stdout2 = archive_symbols(&archive);
    assert!(
        stdout2.contains("cache_mix_probe_a"),
        "build 2 (cache-hit/miss mix) dropped module_a's symbol -- link inputs lost:\n{}",
        stdout2
    );
    assert!(
        stdout2.contains("cache_mix_probe_b"),
        "build 2 (cache-hit/miss mix) dropped module_b's symbol -- link inputs lost:\n{}",
        stdout2
    );
}

/// Widened matrix for issue #64: 6 modules (so rayon's parallel compile path
/// is exercised, not just the trivial single-file case) with 3 touched and 3
/// untouched between builds -- a heavier hit/miss mix than the 2-module case
/// above. Also asserts an exact count of defined probe symbols so a dropped
/// (not just corrupted) object would be caught even if remaining symbols
/// happen to overlap.
#[cfg(target_os = "linux")]
#[test]
fn test_incremental_cache_hit_miss_mix_parallel_wide_matrix() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();

    const N: usize = 6;
    for i in 0..N {
        std::fs::write(
            source_dir.join(format!("wide_mod_{i}.spl")),
            format!("fn wide_cache_mix_probe_{i}() -> i64:\n    return {i}\n"),
        )
        .unwrap();
    }

    let cache_dir = temp.path().join(".simple_native_cache_wide");
    let archive = temp.path().join("libwide_cache_mix.a");

    let make_config = || NativeBuildConfig {
        emit_archive: true,
        incremental: true,
        clean: false,
        no_mangle: true,
        parallel: true,
        cache_dir: Some(cache_dir.clone()),
        ..NativeBuildConfig::default()
    };

    NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(make_config())
        .source_dir(source_dir.clone())
        .build()
        .unwrap();

    // Touch half the modules (alternating) so build 2 mixes cache hits and
    // misses across many files under the parallel compile path.
    for i in 0..N {
        if i % 2 == 0 {
            std::fs::write(
                source_dir.join(format!("wide_mod_{i}.spl")),
                format!("fn wide_cache_mix_probe_{i}() -> i64:\n    return {}\n", i + 1000),
            )
            .unwrap();
        }
    }

    NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
        .config(make_config())
        .source_dir(source_dir.clone())
        .build()
        .unwrap();

    let symbols = std::process::Command::new("nm")
        .arg("-g")
        .arg("--defined-only")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(symbols.status.success(), "nm failed on {}", archive.display());
    let stdout = String::from_utf8_lossy(&symbols.stdout).to_string();

    for i in 0..N {
        let sym = format!("wide_cache_mix_probe_{i}");
        assert!(
            stdout.contains(&sym),
            "build 2 (wide hit/miss mix, parallel) dropped {}:\n{}",
            sym,
            stdout
        );
    }
    let found_count = (0..N)
        .filter(|i| stdout.contains(&format!("wide_cache_mix_probe_{i}")))
        .count();
    assert_eq!(
        found_count, N,
        "expected all {} probe symbols present, found {}",
        N, found_count
    );
}

/// Syntax coverage for the test-only leading-cfg recognizer. Production
/// discovery does not treat this as a whole-file gate because `@cfg` owns one
/// declaration. Covers the documented alias groups
/// (mirroring parser_preprocessor.spl's `_pp_cfg_condition_matches`),
/// `not(...)` negation, and the "leave ungated" cases (no leading @cfg,
/// non-arch condition name, `"key", "value"` pairs) that must NOT be
/// filtered by this discovery-time gate.
#[test]
fn test_file_arch_cfg_gate_recognizes_arch_aliases_and_negation() {
    use super::discovery::file_arch_cfg_gate;
    use simple_common::target::TargetArch;

    // Bare arch aliases: included only for the matching target.
    assert_eq!(
        file_arch_cfg_gate("@cfg(x86_64)\nfn f(): pass\n", TargetArch::X86_64),
        Some(true)
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(x86_64)\nfn f(): pass\n", TargetArch::Riscv64),
        Some(false)
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(riscv64)\nfn f(): pass\n", TargetArch::X86_64),
        Some(false)
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(riscv64)\nfn f(): pass\n", TargetArch::Riscv64),
        Some(true)
    );

    // Alias groups from parser_preprocessor.spl.
    assert_eq!(file_arch_cfg_gate("@cfg(amd64)\n", TargetArch::X86_64), Some(true));
    assert_eq!(file_arch_cfg_gate("@cfg(arm64)\n", TargetArch::Aarch64), Some(true));
    assert_eq!(file_arch_cfg_gate("@cfg(aarch64)\n", TargetArch::Aarch64), Some(true));
    assert_eq!(file_arch_cfg_gate("@cfg(armv7)\n", TargetArch::Arm), Some(true));

    // Negation.
    assert_eq!(
        file_arch_cfg_gate("@cfg(not(riscv64))\nfn f(): pass\n", TargetArch::X86_64),
        Some(true)
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(not(riscv64))\nfn f(): pass\n", TargetArch::Riscv64),
        Some(false)
    );

    // Leading blank lines and comments before the gate are skipped.
    assert_eq!(
        file_arch_cfg_gate("\n# a comment\n\n@cfg(x86_64)\nfn f(): pass\n", TargetArch::X86_64),
        Some(true)
    );

    // Ungated / non-arch conditions must return None (never filtered out).
    assert_eq!(file_arch_cfg_gate("fn f(): pass\n", TargetArch::X86_64), None);
    assert_eq!(
        file_arch_cfg_gate("@cfg(test)\nfn f(): pass\n", TargetArch::X86_64),
        None
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(baremetal)\nfn f(): pass\n", TargetArch::X86_64),
        None
    );
    assert_eq!(
        file_arch_cfg_gate("@cfg(\"target_arch\", \"arm\")\nfn f(): pass\n", TargetArch::X86_64),
        None
    );
}

/// Regression for `x64_freestanding_cfg_multivariant_misdispatch`: six
/// same-named `@cfg(<arch>)` function variants in one compilation unit must
/// collapse to exactly the target's own variant. Before the fix, all six
/// survived and `declare_functions` (codegen/shared.rs) kept whichever was
/// declared FIRST -- source-order, not target-aware -- so a target whose
/// variant was not written first was mis-dispatched. `strip_inactive_cfg_arch_fns`
/// drops the wrong-arch variants so only the target's body remains, and the
/// non-`@cfg` wrapper is always kept.
#[test]
fn test_strip_inactive_cfg_arch_fns_keeps_only_target_variant() {
    use super::discovery::strip_inactive_cfg_arch_fns;
    use simple_common::target::TargetArch;
    use simple_parser::ast::Node;

    // riscv64 is written FIRST, x86_64 LAST -- so a source-order pick would
    // choose the wrong variant for an x86_64 target.
    let src = "\
@cfg(riscv64)\nfn h(): pass\n\
@cfg(riscv32)\nfn h(): pass\n\
@cfg(arm64)\nfn h(): pass\n\
@cfg(arm32)\nfn h(): pass\n\
@cfg(x86)\nfn h(): pass\n\
@cfg(x86_64)\nfn h(): pass\n\
fn wrapper(): h()\n";

    let surviving_cfg_arch = |arch: TargetArch| -> String {
        let mut parser = simple_parser::Parser::new(src);
        let mut module = parser.parse().expect("parse");
        strip_inactive_cfg_arch_fns(&mut module, arch);
        let hs: Vec<&simple_parser::ast::FunctionDef> = module
            .items
            .iter()
            .filter_map(|it| match it {
                Node::Function(f) if f.name == "h" => Some(f),
                _ => None,
            })
            .collect();
        // Exactly one `h` variant survives for the target.
        assert_eq!(hs.len(), 1, "expected one surviving `h` for {arch:?}");
        // The wrapper (no `@cfg`) is always kept.
        assert!(
            module
                .items
                .iter()
                .any(|it| matches!(it, Node::Function(f) if f.name == "wrapper")),
            "wrapper must survive for {arch:?}"
        );
        let cfg_attr = hs[0]
            .attributes
            .iter()
            .find(|a| a.name == "cfg")
            .and_then(|a| a.args.as_ref())
            .and_then(|v| v.first())
            .expect("surviving variant keeps its @cfg");
        format!("{cfg_attr:?}")
    };

    assert!(
        surviving_cfg_arch(TargetArch::X86_64).contains("x86_64"),
        "x86_64 target must keep the x86_64 variant"
    );
    assert!(
        surviving_cfg_arch(TargetArch::Riscv64).contains("riscv64"),
        "riscv64 target must keep the riscv64 variant"
    );
    assert!(
        surviving_cfg_arch(TargetArch::Aarch64).contains("arm64"),
        "aarch64 target must keep the arm64 variant"
    );
}

/// Run-path regression (same bug, `bin/simple run` side): the interpreter
/// executes on the HOST, so after the host-arch strip an entry module with a
/// wrong-arch-first variant ordering must keep only the host's variant, and a
/// module whose every variant is wrong-arch must strip them ALL (the call
/// site then errors instead of silently running a wrong body).
#[test]
fn test_strip_inactive_cfg_arch_fns_for_host_run_path_semantics() {
    use crate::pipeline::cfg_strip::{strip_inactive_cfg_arch_fns_for_host, stripped_fn_hint};
    use simple_common::target::TargetArch;
    use simple_parser::ast::Node;

    let host = TargetArch::host().name();
    let (wrong_a, wrong_b) = if host == "riscv64" {
        ("x86_64", "arm64")
    } else {
        ("riscv64", "riscv32")
    };

    // Wrong-arch variant FIRST, host variant second (declaration-order trap).
    let src = format!("@cfg({wrong_a})\nfn f(): pass\n@cfg({host})\nfn f(): pass\nfn main(): f()\n");
    let mut parser = simple_parser::Parser::new(&src);
    let mut module = parser.parse().expect("parse");
    strip_inactive_cfg_arch_fns_for_host(&mut module);
    let fs: Vec<_> = module
        .items
        .iter()
        .filter_map(|it| match it {
            Node::Function(f) if f.name == "f" => Some(f),
            _ => None,
        })
        .collect();
    assert_eq!(fs.len(), 1, "host strip must keep exactly the host variant");
    assert!(
        format!("{:?}", fs[0].attributes).contains(host),
        "surviving variant must be the host's"
    );

    // NEITHER variant matches the host: both must be stripped (0 survivors),
    // and the stripped-name registry must produce a call-site hint.
    let src = format!("@cfg({wrong_a})\nfn g(): pass\n@cfg({wrong_b})\nfn g(): pass\nfn main(): g()\n");
    let mut parser = simple_parser::Parser::new(&src);
    let mut module = parser.parse().expect("parse");
    strip_inactive_cfg_arch_fns_for_host(&mut module);
    assert!(
        !module
            .items
            .iter()
            .any(|it| matches!(it, Node::Function(f) if f.name == "g")),
        "no wrong-arch variant may survive the host strip"
    );
    let hint = stripped_fn_hint("g").expect("stripped fn must be recorded for the error path");
    assert!(hint.contains("no active @cfg variant"), "hint: {hint}");
    assert!(stripped_fn_hint("never_defined").is_none());
}

/// Full-scan discovery must retain files for per-declaration cfg filtering.
/// A leading inactive declaration is not a whole-file gate.
#[test]
fn test_discover_files_full_scan_keeps_declaration_cfg_files() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_dir = project_root.join("src");
    std::fs::create_dir_all(&src_dir).unwrap();

    std::fs::write(
        src_dir.join("only_x86_64.spl"),
        "@cfg(x86_64)\nfn x86_64_only_probe(): pass\n",
    )
    .unwrap();
    std::fs::write(
        src_dir.join("only_riscv64.spl"),
        "@cfg(riscv64)\nfn riscv64_only_probe(): pass\n",
    )
    .unwrap();
    std::fs::write(src_dir.join("arch_neutral.spl"), "fn neutral_probe(): pass\n").unwrap();
    std::fs::write(
        src_dir.join("mixed.spl"),
        "@cfg(riscv64)\nval ARCH_VALUE = 1\nfn must_still_be_discovered(): pass\n",
    )
    .unwrap();

    let builder = NativeProjectBuilder::new(project_root.clone(), project_root.join("bin/tool")).source_dir(src_dir);

    let files = builder.discover_files().unwrap();
    let names: Vec<String> = files
        .iter()
        .map(|p| p.file_name().unwrap().to_string_lossy().to_string())
        .collect();

    assert!(
        names.contains(&"only_x86_64.spl".to_string()),
        "cfg-decorated declarations are filtered after discovery: {:?}",
        names
    );
    assert!(
        names.contains(&"arch_neutral.spl".to_string()),
        "expected ungated file to always be discovered: {:?}",
        names
    );
    assert!(
        names.contains(&"only_riscv64.spl".to_string()),
        "a declaration cfg must not become a whole-file gate: {:?}",
        names
    );
    assert!(
        names.contains(&"mixed.spl".to_string()),
        "mixed file missing: {:?}",
        names
    );
}

// ---------------------------------------------------------------------------
// Safe-incremental object reuse (SIMPLE_NATIVE_INCREMENTAL=1) — INCR-BUILD lane
// ---------------------------------------------------------------------------

/// Build an all-empty `ImportMapResult` for fingerprint unit tests.
fn empty_import_map_result() -> imports::ImportMapResult {
    imports::ImportMapResult {
        map: std::collections::HashMap::new(),
        ambiguous: std::collections::HashSet::new(),
        all_mangled: std::collections::HashMap::new(),
        re_exports: std::collections::HashMap::new(),
        trait_impls: std::collections::HashMap::new(),
        struct_defs: std::collections::HashMap::new(),
        duplicate_struct_defs: std::collections::HashMap::new(),
        enum_defs: std::collections::HashMap::new(),
        data_exports: std::collections::HashSet::new(),
        data_types: std::collections::HashMap::new(),
        package_data: std::collections::HashMap::new(),
        fn_arities: std::collections::HashMap::new(),
        fn_return_types: std::collections::HashMap::new(),
    }
}

/// The cross-module layout fingerprint must (a) be stable for identical inputs
/// regardless of map iteration order, and (b) change when any cross-module
/// signature/layout input changes. This is the invalidation core that stops a
/// stale wrong-binary reuse under entry-closure.
#[test]
fn test_cross_module_layout_fingerprint_sensitivity_and_stability() {
    // Two independently-built identical maps -> identical fingerprint (the fold
    // is order-independent, so nondeterministic HashMap order cannot bust it).
    let mut a = empty_import_map_result();
    a.fn_arities.insert("alpha".to_string(), 2);
    a.fn_arities.insert("beta".to_string(), 0);
    a.data_exports.insert("SOME_CONST".to_string());

    let mut b = empty_import_map_result();
    // Insert in a different order.
    b.data_exports.insert("SOME_CONST".to_string());
    b.fn_arities.insert("beta".to_string(), 0);
    b.fn_arities.insert("alpha".to_string(), 2);

    assert_eq!(
        cross_module_layout_fingerprint(&a),
        cross_module_layout_fingerprint(&b),
        "identical cross-module inputs must fingerprint identically regardless of insertion order"
    );

    // Changing a signature must change the fingerprint (else a dependent module
    // could stale-reuse an object built against the old signature).
    let mut c = a;
    c.fn_arities.insert("alpha".to_string(), 3);
    assert_ne!(
        cross_module_layout_fingerprint(&b),
        cross_module_layout_fingerprint(&c),
        "an arity change must change the cross-module layout fingerprint"
    );
}

/// The per-build manifest round-trips and names the changed component so a full
/// rebuild is reported with a concrete reason, not a mystery.
#[test]
fn test_global_build_fingerprint_manifest_roundtrip_and_reason() {
    let base = GlobalBuildFingerprint {
        opt_level: 0x1111_1111_1111_1111,
        entry_closure: 0x2222_2222_2222_2222,
        target: 0x3333_3333_3333_3333,
        linker_script: 0x4444_4444_4444_4444,
        layout: 0x5555_5555_5555_5555,
    };
    let line = base.to_manifest_line();
    let parsed = GlobalBuildFingerprint::from_manifest_line(&line).expect("manifest line must parse");
    assert_eq!(parsed, base, "manifest round-trip must preserve all five components");
    assert_eq!(
        base.changed_reason(&parsed),
        None,
        "identical fingerprints report no change"
    );

    let mut layout_changed = base;
    layout_changed.layout = 0x9999_9999_9999_9999;
    assert_eq!(
        layout_changed.changed_reason(&base),
        Some("cross-module type layout / signatures changed")
    );

    let mut ls_changed = base;
    ls_changed.linker_script = 0xABCD_ABCD_ABCD_ABCD;
    assert_eq!(ls_changed.changed_reason(&base), Some("linker script changed"));
}

/// STALENESS REGRESSION GUARD (the critical test): with the safe-incremental
/// path on, a leaf body change reuses untouched modules (incrementality works),
/// but a CROSS-MODULE struct-layout change in module A invalidates the entire
/// per-module cache so module B — whose object bytes depend on A's field
/// offsets via `populate_global_struct_defs` — is never stale-reused.
///
/// Red/green: with the legacy content-only key (`incremental_hardening=false`)
/// the struct-change build would leave module B cached (`cached >= 1`) and ship a
/// stale wrong binary. The hardened key drives `cached == 0`. Verified manually
/// that flipping the flag off makes the final assertion fail.
#[cfg(target_os = "linux")]
#[test]
fn test_incremental_hardening_invalidates_on_cross_module_struct_change() {
    let temp = tempfile::tempdir().unwrap();
    let source_dir = temp.path().join("src");
    std::fs::create_dir_all(&source_dir).unwrap();

    let module_a = source_dir.join("layout_a.spl");
    let module_b = source_dir.join("reader_b.spl");
    // Module A owns the shared struct; module B reads a field of it, so B's
    // codegen depends on A's field offsets (cross-module layout dependency).
    let write_a = |extra: bool| {
        let fields = if extra {
            "    pad: i64\n    extra: i64\n    tag: i64\n"
        } else {
            "    pad: i64\n    tag: i64\n"
        };
        std::fs::write(
            &module_a,
            format!("struct SharedLayout:\n{fields}\nfn shared_layout_origin() -> i64:\n    return 111\n"),
        )
        .unwrap();
    };
    write_a(false);
    std::fs::write(
        &module_b,
        "fn shared_layout_reader(p: SharedLayout) -> i64:\n    return p.tag\n",
    )
    .unwrap();

    let cache_dir = temp.path().join(".native_cache_incr");
    let archive = temp.path().join("libincr_probe.a");
    let make_config = || NativeBuildConfig {
        emit_archive: true,
        incremental: true,
        incremental_hardening: true,
        clean: false,
        no_mangle: false,
        cache_dir: Some(cache_dir.clone()),
        ..NativeBuildConfig::default()
    };
    let build = || {
        NativeProjectBuilder::new(temp.path().to_path_buf(), archive.clone())
            .config(make_config())
            .source_dir(source_dir.clone())
            .build()
            .expect("native build failed")
    };

    // Build 1: cold cache -> both modules compile fresh.
    let r1 = build();
    assert_eq!(r1.cached, 0, "cold build must not report cache hits");
    assert!(
        r1.compiled >= 2,
        "cold build must compile both modules, got {}",
        r1.compiled
    );

    // Build 2: leaf body-only change in A (constant), B untouched. B stays cached
    // -> incrementality is real (not a full rebuild on every edit).
    std::fs::write(
        &module_a,
        "struct SharedLayout:\n    pad: i64\n    tag: i64\n\nfn shared_layout_origin() -> i64:\n    return 222\n",
    )
    .unwrap();
    let r2 = build();
    assert!(
        r2.cached >= 1,
        "a leaf body change must still reuse the untouched module (incrementality lost): cached={}",
        r2.cached
    );

    // Build 3: CROSS-MODULE struct-layout change in A (insert a field before
    // `tag`, shifting B's read offset). The global build fingerprint changes, so
    // the entire per-module cache is invalidated and B is rebuilt -- never a
    // stale reuse. This is the assertion the legacy content-only key fails.
    write_a(true);
    let r3 = build();
    assert_eq!(
        r3.cached, 0,
        "a cross-module struct-layout change must invalidate the whole cache (no stale reuse); got cached={}",
        r3.cached
    );
}
