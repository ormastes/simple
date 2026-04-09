//! Tests for native project builder.

use std::path::PathBuf;

use crate::codegen::common_backend::module_prefix_from_path;
use crate::incremental::SourceInfo;
use super::*;

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
fn test_incremental_cache_dir_custom() {
    let mut config = NativeBuildConfig::default();
    config.cache_dir = Some(PathBuf::from("/tmp/my_cache"));

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
fn test_runtime_bundle_auto_prefers_runtime_for_non_compiler_entry() {
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig::default();
    config.runtime_path = Some(temp.path().to_path_buf());

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/t32_mcp_native"))
            .config(config);
    builder.entry_file = Some(PathBuf::from("/project/examples/10_tooling/trace32_tools/t32_mcp/frontend_light.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap();
    assert_eq!(selected, runtime);
    assert!(!is_native_all);
}

#[test]
fn test_runtime_bundle_auto_prefers_native_all_for_compiler_entry() {
    let temp = tempfile::tempdir().unwrap();
    let runtime = temp.path().join("libsimple_runtime.a");
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&runtime, b"runtime").unwrap();
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig::default();
    config.runtime_path = Some(temp.path().to_path_buf());

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/simple_native"))
            .config(config);
    builder.entry_file = Some(PathBuf::from("/project/src/app/cli/main.spl"));

    let (selected, is_native_all) = builder.selected_runtime_library(temp.path()).unwrap();
    assert_eq!(selected, native_all);
    assert!(is_native_all);
}

#[test]
fn test_runtime_bundle_auto_rejects_native_all_for_non_compiler_entry() {
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig::default();
    config.runtime_path = Some(temp.path().to_path_buf());

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/t32_lsp_mcp_tool_runner"))
            .config(config);
    builder.entry_file = Some(PathBuf::from(
        "/project/examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl",
    ));

    let selected_runtime = builder.selected_runtime_library(temp.path());
    let err = builder
        .reject_unexpected_native_all(selected_runtime.as_ref())
        .unwrap_err();
    assert!(err.contains("refused oversized runtime bundle"));
    assert!(err.contains("tool_runner.spl"));
}

#[test]
fn test_runtime_bundle_all_allows_native_all_for_non_compiler_entry() {
    let temp = tempfile::tempdir().unwrap();
    let native_all = temp.path().join("libsimple_native_all.a");
    std::fs::write(&native_all, b"all").unwrap();

    let mut config = NativeBuildConfig::default();
    config.runtime_path = Some(temp.path().to_path_buf());
    config.runtime_bundle = "all".to_string();

    let mut builder =
        NativeProjectBuilder::new(PathBuf::from("/project"), PathBuf::from("/project/bin/t32_lsp_mcp_tool_runner"))
            .config(config);
    builder.entry_file = Some(PathBuf::from(
        "/project/examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl",
    ));

    let selected_runtime = builder.selected_runtime_library(temp.path());
    builder
        .reject_unexpected_native_all(selected_runtime.as_ref())
        .unwrap();
}
