//! Build configuration: runtime bundle selection, runtime library discovery.

use std::path::{Path, PathBuf};

use simple_common::target::LinkerFlavor;

use super::tools::{
    archive_defined_symbols, build_core_c_runtime_library, find_abi_complete_simple_core_runtime_library,
    find_core_c_runtime_source_root, find_runtime_library, find_simple_core_runtime_library,
    runtime_archive_has_core_required_symbols, runtime_authority_search_dirs,
};

use super::NativeProjectBuilder;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NativeRuntimeLane {
    SimpleCore,
    CoreCBootstrap,
    HostGpu,
}

impl NativeRuntimeLane {
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::SimpleCore => "simple-core",
            Self::CoreCBootstrap => "core-c-bootstrap",
            Self::HostGpu => "host-gpu",
        }
    }
}

fn runtime_bundle_requests_simple_core(value: &str) -> bool {
    matches!(value, "simple-core" | "simple_core")
}

fn runtime_bundle_requests_core_c_bootstrap(value: &str) -> bool {
    matches!(
        value,
        "core-c-bootstrap" | "core_c_bootstrap" | "runtime" | "core" | "core-c" | "core_c"
    )
}

fn runtime_bundle_requests_host_gpu(value: &str) -> bool {
    matches!(value, "host-gpu" | "host_gpu" | "gpu")
}

fn runtime_bundle_requests_hosted(value: &str) -> bool {
    matches!(
        value,
        "all" | "hosted" | "rust-hosted" | "hosted-runtime" | "rust-runtime"
    )
}

fn runtime_archive_names(flavor: LinkerFlavor) -> (&'static str, &'static str) {
    match flavor {
        LinkerFlavor::Msvc => ("simple_native_all.lib", "simple_runtime.lib"),
        LinkerFlavor::Gnu | LinkerFlavor::WasmLd => ("libsimple_native_all.a", "libsimple_runtime.a"),
    }
}

fn is_compiler_like_entry(path: &Path) -> bool {
    let p = path.to_string_lossy().replace('\\', "/");
    p.contains("/src/compiler/")
        || p.ends_with("/src/compiler")
        || p.contains("/src/app/cli/")
        || p.ends_with("/src/app/cli")
}

pub(super) fn is_bootstrap_main_entry(path: &Option<PathBuf>) -> bool {
    std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1")
        && path.as_ref().and_then(|p| p.file_name()).and_then(|name| name.to_str()) == Some("bootstrap_main.spl")
}

/// Provision the hosted `libsimple_native_all.a` authority for the bootstrap
/// CLI entry.
///
/// `src/app/cli/bootstrap_main.spl:2` declares `extern fn rt_native_build`, and
/// the ONLY implementation of that symbol in the tree is the hosted Rust
/// `simple-native-all` crate (`src/compiler_rust/native_all/src/lib.rs:143`).
/// There is no C body and there cannot be one -- it IS the native-build driver.
/// So this is a runtime-lane SELECTION requirement, never a reason to widen the
/// Simple/C core ABI with a symbol the core lane cannot implement.
///
/// `selected_runtime_library` already authorised the hosted archive for exactly
/// this entry (`is_bootstrap_main_entry`), but the branch was reachable only
/// when an explicit `--runtime-path` was supplied. The bare `build bootstrap`
/// stage driver never supplies one, so Stage 1 fell through to the
/// core-c-bootstrap lane and died with `undefined reference to rt_native_build`.
/// This resolves the authority rather than leaving it unset.
///
/// Deliberately NOT a cwd-relative scan of `src/compiler_rust/target` --
/// `find_native_all_library` returns `None` on purpose and a test pins that.
/// Every source here is an EXPLICIT authority (operator-supplied path, env
/// override, the running seed's own install dir) or an archive this function
/// builds itself from the crate that owns the symbol.
fn bootstrap_hosted_native_all_runtime(
    runtime_path: Option<&Path>,
    native_all_name: &str,
    temp_dir: &Path,
) -> Option<PathBuf> {
    fn usable(path: PathBuf) -> Option<PathBuf> {
        // An empty placeholder archive is not an authority.
        match std::fs::metadata(&path) {
            Ok(meta) if meta.is_file() && meta.len() > 0 => Some(path),
            _ => None,
        }
    }

    let mut roots: Vec<PathBuf> = Vec::new();
    if let Some(rp) = runtime_path {
        roots.push(rp.to_path_buf());
    }
    if let Some(dir) = super::RUNTIME_PATH_OVERRIDE.get() {
        roots.push(dir.clone());
    }
    if let Ok(env_path) = std::env::var("SIMPLE_RUNTIME_PATH") {
        if !env_path.is_empty() {
            roots.push(PathBuf::from(env_path));
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            roots.push(dir.to_path_buf());
            roots.push(dir.join("runtime-authority"));
        }
    }

    for root in &roots {
        for dir in runtime_authority_search_dirs(root) {
            if let Some(found) = usable(dir.join(native_all_name)) {
                return Some(found);
            }
        }
    }

    build_bootstrap_hosted_native_all_archive(native_all_name, temp_dir).and_then(usable)
}

/// Last resort for `bootstrap_hosted_native_all_runtime`: build the hosted
/// archive from the crate that defines `rt_native_build`, into a build dir of
/// our own. Mirrors `build_core_c_runtime_library`'s "provision it yourself"
/// contract for the core lane, one level up.
fn build_bootstrap_hosted_native_all_archive(native_all_name: &str, temp_dir: &Path) -> Option<PathBuf> {
    let repo_root = find_core_c_runtime_source_root()?.parent()?.parent()?.to_path_buf();
    let manifest = repo_root.join("src").join("compiler_rust").join("Cargo.toml");
    if !manifest.is_file() {
        return None;
    }
    let target_dir = temp_dir.join("hosted_native_all");
    let status = std::process::Command::new("cargo")
        .arg("build")
        .arg("--release")
        .arg("--manifest-path")
        .arg(&manifest)
        .arg("-p")
        .arg("simple-native-all")
        .env("CARGO_TARGET_DIR", &target_dir)
        .status()
        .ok()?;
    if !status.success() {
        return None;
    }
    let built = target_dir.join("release").join(native_all_name);
    if built.is_file() { Some(built) } else { None }
}

fn runtime_path_has_abi_complete_simple_core(runtime_path: Option<&Path>) -> bool {
    runtime_path.is_some_and(|path| {
        ["simple-core", "simple_core"].iter().any(|lane_dir| {
            let dir = path.join(lane_dir);
            [
                dir.join("deps").join("libsimple_runtime.a"),
                dir.join("libsimple_runtime.a"),
            ]
            .iter()
            .any(|candidate| candidate.exists() && runtime_archive_has_core_required_symbols(candidate))
        })
    })
}

pub(crate) fn runtime_archive_has_bootstrap_cli_symbols(path: &Path) -> bool {
    let Some(symbols) = archive_defined_symbols(path) else {
        return false;
    };
    [
        "rt_get_args",
        "rt_cli_get_args",
        "rt_array_len",
        "rt_array_get",
        "rt_array_get_text",
        "rt_string_len",
        "rt_string_data",
        "rt_file_read_text",
        "rt_process_run",
    ]
    .iter()
    .all(|symbol| symbols.contains(symbol.trim_start_matches('_')))
}

impl NativeProjectBuilder {
    pub(crate) fn is_authorized_stage4_compiler_entry(&self) -> bool {
        if !cfg!(any(target_os = "linux", target_os = "macos")) {
            return false;
        }
        let Some(entry) = self.entry_file.as_ref().map(|entry| super::safe_canonicalize(entry)) else {
            return false;
        };
        if std::env::var("SIMPLE_COMPILER_ENTRY_STAGE4").as_deref() == Ok("1")
            && entry == super::safe_canonicalize(&self.project_root.join("src/compiler/80.driver/main.spl"))
        {
            return true;
        }
        if std::env::var("SIMPLE_BOOTSTRAP").as_deref() != Ok("1")
            || std::env::var("SIMPLE_BOOTSTRAP_STAGE4").as_deref() != Ok("1")
        {
            return false;
        }
        [
            "src/app/cli/main.spl",
            "src/app/cli/native_build_main.spl",
            "src/app/os/main.spl",
        ]
        .iter()
        .any(|expected| entry == super::safe_canonicalize(&self.project_root.join(expected)))
    }

    pub(crate) fn selected_stage4_compiler_backfill_archive(&self) -> Result<Option<PathBuf>, String> {
        if !self.is_authorized_stage4_compiler_entry() {
            return Ok(None);
        }
        let runtime_path = self
            .config
            .runtime_path
            .as_ref()
            .ok_or_else(|| "Stage4 compiler entry requires an explicit runtime path".to_string())?;
        let archive = runtime_path.join("libsimple_compiler_backfill.a");
        if !archive.is_file() {
            return Err(format!(
                "Stage4 compiler backfill archive is missing: {}",
                archive.display()
            ));
        }
        Ok(Some(archive))
    }

    pub(crate) fn runtime_bundle_prefers_core_lane(&self) -> bool {
        true
    }

    pub(crate) fn resolve_runtime_lane(&self) -> NativeRuntimeLane {
        match self.config.runtime_bundle.as_str() {
            value if runtime_bundle_requests_simple_core(value) => return NativeRuntimeLane::SimpleCore,
            value if runtime_bundle_requests_core_c_bootstrap(value) => return NativeRuntimeLane::CoreCBootstrap,
            value if runtime_bundle_requests_host_gpu(value) => return NativeRuntimeLane::HostGpu,
            _ => {}
        }
        if std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_simple_core)
        {
            return NativeRuntimeLane::SimpleCore;
        }
        if std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_core_c_bootstrap)
        {
            return NativeRuntimeLane::CoreCBootstrap;
        }
        if let Some(runtime_path) = self.config.runtime_path.as_deref() {
            return if runtime_path_has_abi_complete_simple_core(Some(runtime_path)) {
                NativeRuntimeLane::SimpleCore
            } else {
                NativeRuntimeLane::CoreCBootstrap
            };
        }
        if find_abi_complete_simple_core_runtime_library().is_some() {
            NativeRuntimeLane::SimpleCore
        } else {
            NativeRuntimeLane::CoreCBootstrap
        }
    }

    pub(crate) fn runtime_bundle_requests_removed_hosted(&self) -> bool {
        if runtime_bundle_requests_hosted(&self.config.runtime_bundle) {
            return true;
        }
        std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_hosted)
    }

    pub(crate) fn runtime_bundle_is_explicit_simple_core(&self) -> bool {
        if runtime_bundle_requests_simple_core(&self.config.runtime_bundle) {
            return true;
        }
        std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_simple_core)
    }

    pub(crate) fn reject_unexpected_native_all(
        &self,
        selected_runtime: Option<&(PathBuf, bool)>,
    ) -> Result<(), String> {
        if let Some((runtime_lib, true)) = selected_runtime {
            if is_bootstrap_main_entry(&self.entry_file) || self.resolve_runtime_lane() == NativeRuntimeLane::HostGpu {
                return Ok(());
            }
            let entry = self
                .entry_file
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "<none>".to_string());
            return Err(format!(
                "native-build refused hosted native_all runtime for `{}` on the `{}` lane: selected `{}`. Use `--runtime-bundle simple-core` with an ABI-complete pure Simple archive or `--runtime-bundle core-c-bootstrap` for the C bootstrap runtime.",
                entry,
                self.resolve_runtime_lane().display_name(),
                runtime_lib.display()
            ));
        }
        Ok(())
    }

    pub(crate) fn selected_runtime_library(&self, temp_dir: &Path) -> Result<Option<(PathBuf, bool)>, String> {
        let bootstrap_hosted = is_bootstrap_main_entry(&self.entry_file) || self.is_authorized_stage4_compiler_entry();
        if self.runtime_bundle_requests_removed_hosted() && !bootstrap_hosted {
            return Err(
                "native-build removed Rust-hosted runtime bundles; use simple-core or core-c-bootstrap".to_string(),
            );
        }
        let lane = self.resolve_runtime_lane();
        if self.is_authorized_stage4_compiler_entry() {
            if lane != NativeRuntimeLane::CoreCBootstrap {
                return Err("Stage4 compiler entry requires the core-c-bootstrap runtime lane".to_string());
            }
            let core_dir = temp_dir.join("core_c_runtime");
            let core = build_core_c_runtime_library(&core_dir)
                .ok_or_else(|| "failed to build the Stage4 core-C runtime archive".to_string())?;
            return Ok(Some((core, false)));
        }
        let mut candidates: Vec<(PathBuf, bool)> = Vec::new();
        let (native_all_name, runtime_name) = runtime_archive_names(super::effective_target().linker_flavor());

        if is_bootstrap_main_entry(&self.entry_file) {
            if let Some(native_all) =
                bootstrap_hosted_native_all_runtime(self.config.runtime_path.as_deref(), native_all_name, temp_dir)
            {
                return Ok(Some((native_all, true)));
            }
        }

        if runtime_bundle_requests_host_gpu(&self.config.runtime_bundle) {
            let provider = self
                .config
                .runtime_path
                .as_ref()
                .and_then(|path| {
                    runtime_authority_search_dirs(path)
                        .into_iter()
                        .map(|dir| dir.join(runtime_name))
                        .find(|candidate| candidate.is_file())
                })
                .ok_or_else(|| {
                    "native-build requested host-gpu but a feature-built libsimple_runtime.a is missing".to_string()
                })?;
            let symbols = archive_defined_symbols(&provider).ok_or_else(|| {
                format!(
                    "native-build could not inspect host-gpu runtime archive `{}`",
                    provider.display()
                )
            })?;
            let missing = simple_common::RUNTIME_SYMBOL_NAMES
                .iter()
                .copied()
                .filter(|symbol| symbol.starts_with("rt_host_gpu_queue_") && !symbols.contains(*symbol))
                .collect::<Vec<_>>();
            if !missing.is_empty() {
                return Err(format!(
                    "native-build host-gpu runtime archive `{}` is missing Engine2D queue symbols: {}",
                    provider.display(),
                    missing.join(", ")
                ));
            }
            return Ok(Some((provider, false)));
        }

        // A source checkout is authoritative for the explicit core-C lane.
        // A runtime path beside a staged compiler may contain the Rust hosted
        // `libsimple_runtime.a`; its small bootstrap-CLI symbol prefix is not
        // proof that it provides mutex, thread, or piped-process entry points
        // required by an arbitrary application closure. Build the complete
        // core-C archive from the checked-out sources before considering a
        // prebuilt fallback. Deployed compilers without `src/runtime` retain
        // the fallback path below.
        if lane == NativeRuntimeLane::CoreCBootstrap && find_core_c_runtime_source_root().is_some() {
            let core_c_dir = temp_dir.join("core_c_runtime");
            let runtime = build_core_c_runtime_library(&core_c_dir).ok_or_else(|| {
                format!(
                    "native-build could not build the core-C runtime archive in {}",
                    core_c_dir.display()
                )
            })?;
            return Ok(Some((runtime, false)));
        }

        let mut saw_core_c_runtime_path_archive = false;
        let mut push_runtime_candidates = |dir: &Path| {
            let runtime_deps = dir.join("deps").join(runtime_name);
            let runtime = dir.join(runtime_name);
            match lane {
                NativeRuntimeLane::CoreCBootstrap => {
                    if runtime_deps.exists() {
                        saw_core_c_runtime_path_archive = true;
                        if runtime_archive_has_bootstrap_cli_symbols(&runtime_deps) {
                            candidates.push((runtime_deps, false));
                        }
                    }
                    if runtime.exists() {
                        saw_core_c_runtime_path_archive = true;
                        if runtime_archive_has_bootstrap_cli_symbols(&runtime) {
                            candidates.push((runtime, false));
                        }
                    }
                }
                NativeRuntimeLane::SimpleCore => {
                    for lane_dir in ["simple-core", "simple_core"] {
                        let candidate_dir = dir.join(lane_dir);
                        let lane_runtime_deps = candidate_dir.join("deps").join(runtime_name);
                        let lane_runtime = candidate_dir.join(runtime_name);
                        if lane_runtime_deps.exists() {
                            candidates.push((lane_runtime_deps, false));
                        }
                        if lane_runtime.exists() {
                            candidates.push((lane_runtime, false));
                        }
                    }
                }
                NativeRuntimeLane::HostGpu => {}
            }
        };

        if let Some(ref rp) = self.config.runtime_path {
            push_runtime_candidates(rp);
        } else {
            match lane {
                NativeRuntimeLane::SimpleCore => {
                    if let Some(runtime) = find_abi_complete_simple_core_runtime_library() {
                        candidates.push((runtime, false));
                    }
                }
                NativeRuntimeLane::CoreCBootstrap => {
                    // When the core-C archive fails to build we still link whatever
                    // find_runtime_library() turns up -- a generic runtime roughly 28x
                    // larger. Say so here; otherwise the only symptom is a binary-size
                    // assertion far away from the real cause.
                    let core_c_dir = temp_dir.join("core_c_runtime");
                    match build_core_c_runtime_library(&core_c_dir) {
                        Some(runtime) => candidates.push((runtime, false)),
                        // In a source checkout the core-C archive MUST build; a failure
                        // there is a toolchain defect, not a supported configuration.
                        // Falling through to find_runtime_library() links a generic
                        // archive ~28x larger and only surfaces as a distant
                        // binary-size assertion. A deployed compiler ships a prebuilt
                        // core-c-bootstrap archive and has no src/runtime, so it
                        // legitimately keeps the fallback.
                        None if find_core_c_runtime_source_root().is_some() => {
                            return Err(format!(
                                "native-build could not build the core-C runtime archive in {}. \
                                 core-C runtime sources are present, so this is a toolchain \
                                 failure rather than a missing prebuilt runtime. Re-run with \
                                 SIMPLE_NATIVE_BUILD_RUST_TRACE=1 to see the failing compile.",
                                core_c_dir.display()
                            ));
                        }
                        None => eprintln!(
                            "warning: no core-C runtime sources found; falling back to a \
                             prebuilt runtime from find_runtime_library() (expect a much \
                             larger binary if it is not the core-c-bootstrap lane)"
                        ),
                    }
                    if let Some(runtime) = find_runtime_library() {
                        if !candidates.iter().any(|(p, _)| p == &runtime) {
                            candidates.push((runtime, false));
                        }
                    }
                }
                NativeRuntimeLane::HostGpu => {}
            }
        }

        if lane == NativeRuntimeLane::CoreCBootstrap
            && candidates.is_empty()
            && (self.config.runtime_path.is_none() || saw_core_c_runtime_path_archive)
        {
            if let Some(runtime) = build_core_c_runtime_library(&temp_dir.join("core_c_runtime")) {
                candidates.push((runtime, false));
            }
            if let Some(runtime) = find_runtime_library() {
                if runtime_archive_has_bootstrap_cli_symbols(&runtime) && !candidates.iter().any(|(p, _)| p == &runtime)
                {
                    candidates.push((runtime, false));
                }
            }
        }

        if let Some(selected) = candidates.into_iter().next() {
            return Ok(Some(selected));
        }

        if self.runtime_bundle_is_explicit_simple_core() {
            let entry = self
                .entry_file
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "<none>".to_string());
            return Err(format!(
                "native-build requested `simple-core` for `{}` but no simple-core runtime archive was found. Provide SIMPLE_SIMPLE_CORE_PATH/SIMPLE_CORE_RUNTIME_PATH or use `--runtime-bundle core-c-bootstrap` while the pure-Simple lane is still being ported.",
                entry
            ));
        }

        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_archive_names_follow_linker_flavor() {
        assert_eq!(
            runtime_archive_names(LinkerFlavor::Gnu),
            ("libsimple_native_all.a", "libsimple_runtime.a")
        );
        assert_eq!(
            runtime_archive_names(LinkerFlavor::Msvc),
            ("simple_native_all.lib", "simple_runtime.lib")
        );
    }
}
