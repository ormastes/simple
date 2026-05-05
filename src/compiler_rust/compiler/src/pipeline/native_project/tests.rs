//! Tests for native project builder.

use std::fs;
use std::path::PathBuf;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use crate::codegen::common_backend::module_prefix_from_path;
use crate::incremental::SourceInfo;
use simple_simd::{host_cpu_config, reset_host_cpu_config_cache_for_tests, HostCpuConfig, SimdTier};
use super::*;

fn simd_tier_env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn process_dir_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn runtime_bundle_env_lock() -> &'static Mutex<()> {
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
fn test_incremental_cache_dir_default() {
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"));
    assert_eq!(builder.cache_dir(), PathBuf::from("/project/.simple/native_cache"));
}

#[test]
fn test_source_dir_preserves_logical_path() {
    let builder = NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple"))
        .source_dir(PathBuf::from("src/app/mcp_t32"));
    assert_eq!(builder.source_dirs, vec![PathBuf::from("/project/src/app/mcp_t32")]);
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
    assert_eq!(selected, runtime);
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_auto_prefers_hosted_runtime_for_compiler_entry() {
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
    assert_eq!(selected, native_all);
    assert!(is_native_all);
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
    assert_eq!(selected, runtime);
    assert!(!is_native_all);
}

#[test]
fn test_core_lane_runtime_archives_expose_required_abi_symbols() {
    let _guard = runtime_bundle_env_lock().lock().unwrap();
    let temp = tempfile::tempdir().unwrap();

    let core_c = build_core_c_runtime_library(temp.path()).expect("core-c runtime archive should build");
    assert!(
        runtime_archive_has_core_required_symbols(&core_c),
        "core-c runtime archive is missing one or more core-required ABI symbols: {}",
        core_c.display()
    );

    if let Some(simple_core) = find_simple_core_runtime_library() {
        assert!(
            runtime_archive_has_core_required_symbols(&simple_core),
            "discovered simple-core runtime archive is not ABI-complete: {}",
            simple_core.display()
        );
    }
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
    assert!(output.status.success(), "{label} ABI probe exited unsuccessfully");
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
fn test_find_native_all_library_skips_empty_debug_archive() {
    let temp = tempfile::tempdir().unwrap();
    let debug_dir = temp.path().join("src/compiler_rust/target/debug");
    let release_dir = temp.path().join("src/compiler_rust/target/release");
    std::fs::create_dir_all(&debug_dir).unwrap();
    std::fs::create_dir_all(&release_dir).unwrap();

    let empty_debug = debug_dir.join("libsimple_native_all.a");
    let release = release_dir.join("libsimple_native_all.a");
    std::fs::write(&empty_debug, b"").unwrap();
    std::fs::write(&release, b"real archive").unwrap();

    let selected = with_current_dir(temp.path(), find_native_all_library).unwrap();
    assert_eq!(
        selected,
        PathBuf::from("src/compiler_rust/target/release/libsimple_native_all.a")
    );
}

#[test]
fn test_runtime_bundle_auto_rejects_native_all_for_non_compiler_entry() {
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
    let err = builder
        .reject_unexpected_native_all(selected_runtime.as_ref())
        .unwrap_err();
    assert!(err.contains("core-c-bootstrap"));
    assert!(err.contains("--runtime-bundle rust-hosted"));
    assert!(err.contains("tool_runner.spl"));
}

#[test]
fn test_runtime_bundle_hosted_allows_native_all_for_non_compiler_entry() {
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

    let selected_runtime = builder.selected_runtime_library(temp.path()).unwrap();
    builder.reject_unexpected_native_all(selected_runtime.as_ref()).unwrap();
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
fn test_runtime_bundle_legacy_all_alias_allows_native_all_for_non_compiler_entry() {
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

    let selected_runtime = builder.selected_runtime_library(temp.path()).unwrap();
    builder.reject_unexpected_native_all(selected_runtime.as_ref()).unwrap();
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
fn test_duplicate_struct_sidecar_resolves_unique_compiler_context_handle() {
    let temp = tempfile::tempdir().unwrap();
    let project_root = temp.path().join("project");
    let src_root = project_root.join("src");
    let compiler_root = src_root.join("compiler");
    std::fs::create_dir_all(compiler_root.join("99.loader/loader")).unwrap();
    std::fs::create_dir_all(compiler_root.join("99.loader")).unwrap();
    std::fs::create_dir_all(compiler_root.join("70.backend/linker")).unwrap();

    let alive_ctx = compiler_root.join("99.loader/compiler_ffi.spl");
    let handle_ctx = compiler_root.join("99.loader/loader/compiler_ffi.spl");
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
        .any(|fields| fields == &vec![("handle".to_string(), "Simple(\"i64\")".to_string())]));

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
fn test_runtime_retention_symbols_include_object_undefineds_and_roots() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let runtime_c = temp.path().join("runtime.c");
    let app_c = temp.path().join("app.c");
    let runtime_o = temp.path().join("runtime.o");
    let app_o = temp.path().join("app.o");

    std::fs::write(
        &runtime_c,
        r#"
void rt_used(void) {}
void rt_unused(void) {}
void __simple_runtime_init(void) {}
void __simple_runtime_shutdown(void) {}
void rt_set_args(void) {}
void rt_function_not_found(void) {}
void rt_string_new(void) {}
void rt_string_data(void) {}
void rt_string_len(void) {}
void rt_array_new(void) {}
void rt_array_len(void) {}
"#,
    )
    .unwrap();
    std::fs::write(
        &app_c,
        r#"
extern void rt_used(void);
void app_call(void) { rt_used(); }
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
    assert!(std::process::Command::new(&cc)
        .args(["-c", "-ffunction-sections", "-fdata-sections"])
        .arg(&app_c)
        .arg("-o")
        .arg(&app_o)
        .status()
        .unwrap()
        .success());

    let imports = ModuleImports {
        import_map: std::sync::Arc::new(std::collections::HashMap::new()),
        ambiguous_names: std::sync::Arc::new(std::collections::HashSet::new()),
        all_mangled: std::sync::Arc::new(std::collections::HashMap::new()),
        re_exports: std::sync::Arc::new(std::collections::HashMap::new()),
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let roots =
        NativeProjectBuilder::runtime_retention_symbols(&[app_o.clone()], &app_o, None, &runtime_o, &imports).unwrap();

    assert!(roots.contains(&"rt_used".to_string()));
    assert!(roots.contains(&"__simple_runtime_init".to_string()));
    assert!(roots.contains(&"rt_function_not_found".to_string()));
    assert!(!roots.contains(&"rt_unused".to_string()));
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
    assert!(!super::tools::is_system_symbol("app__mcp__main"));
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
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    };

    let stub_o = super::stubs::generate_stub_object(temp.path(), &[], &main_o, None, &imports).unwrap();
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
        "archive symbols did not include known runtime-FFI parameterized function:\n{}",
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
    assert!(
        runtime_archive_has_core_required_symbols(&archive),
        "pure-Simple source tree must now satisfy the core-required ABI"
    );

    let symbols = std::process::Command::new("nm")
        .arg("-g")
        .arg("--defined-only")
        .arg(&archive)
        .output()
        .unwrap();
    assert!(symbols.status.success());
    let stdout = String::from_utf8_lossy(&symbols.stdout);
    for symbol in [
        "__simple_runtime_init",
        "__simple_runtime_shutdown",
        "rt_value_int",
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
        "rt_array_len",
        "rt_array_get",
        "rt_array_set",
        "rt_array_push",
        "rt_array_pop",
        "rt_string_new",
        "rt_string_len",
        "rt_string_data",
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
    if (rt_value_int(7) != 56) return 10;
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
    if (rt_array_get(a, rt_value_int(1)) != rt_value_int(20)) return 46;
    rt_array_set(a, -1, rt_value_int(30));
    if (rt_array_get(a, 1) != rt_value_int(30)) return 47;
    extern int64_t rt_array_pop(SplArray*);
    if (rt_array_pop(a) != rt_value_int(30)) return 48;
    if (rt_array_len(a) != 1) return 49;
    if (rt_array_get(a, 99) != 3) return 50;

    int64_t s = rt_string_new((const uint8_t*)" 123 ", 5);
    if (rt_string_len(s) != 5) return 60;
    if (memcmp(rt_string_data(s), " 123 ", 5) != 0) return 61;
    if (rt_len(s) != 5) return 62;
    int64_t t = rt_string_new((const uint8_t*)"abc", 3);
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
        struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        duplicate_struct_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        enum_defs: std::sync::Arc::new(std::collections::HashMap::new()),
        data_exports: std::sync::Arc::new(std::collections::HashSet::new()),
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
