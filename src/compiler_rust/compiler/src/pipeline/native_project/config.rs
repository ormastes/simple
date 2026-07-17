//! Build configuration: runtime bundle selection, runtime library discovery.

use std::path::{Path, PathBuf};

use super::tools::{
    archive_defined_symbols, build_core_c_runtime_library, find_abi_complete_simple_core_runtime_library,
    find_runtime_library, find_simple_core_runtime_library, runtime_archive_has_core_required_symbols,
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

fn is_compiler_like_entry(path: &Path) -> bool {
    let p = path.to_string_lossy().replace('\\', "/");
    p.contains("/src/compiler/")
        || p.ends_with("/src/compiler")
        || p.contains("/src/app/cli/")
        || p.ends_with("/src/app/cli")
}

fn is_bootstrap_main_entry(path: &Option<PathBuf>) -> bool {
    std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1")
        && path.as_ref().and_then(|p| p.file_name()).and_then(|name| name.to_str()) == Some("bootstrap_main.spl")
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
        if !cfg!(any(target_os = "linux", target_os = "macos"))
            || std::env::var("SIMPLE_BOOTSTRAP").as_deref() != Ok("1")
            || std::env::var("SIMPLE_BOOTSTRAP_STAGE4").as_deref() != Ok("1")
        {
            return false;
        }
        let Some(entry) = self.entry_file.as_ref().map(|entry| super::safe_canonicalize(entry)) else {
            return false;
        };
        ["src/app/cli/main.spl", "src/app/cli/native_build_main.spl"]
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
        let native_all_name = if cfg!(target_os = "windows") {
            "simple_native_all.lib"
        } else {
            "libsimple_native_all.a"
        };
        let runtime_name = if cfg!(target_os = "windows") {
            "simple_runtime.lib"
        } else {
            "libsimple_runtime.a"
        };

        if is_bootstrap_main_entry(&self.entry_file) {
            if let Some(ref rp) = self.config.runtime_path {
                let native_all = rp.join(native_all_name);
                if native_all.exists() {
                    return Ok(Some((native_all, true)));
                }
            }
        }

        if runtime_bundle_requests_host_gpu(&self.config.runtime_bundle) {
            let provider = self
                .config
                .runtime_path
                .as_ref()
                .and_then(|path| {
                    [
                        path.join("bootstrap").join("deps").join("libsimple_runtime.a"),
                        path.join("bootstrap").join("libsimple_runtime.a"),
                        path.join("deps").join("libsimple_runtime.a"),
                        path.join("libsimple_runtime.a"),
                    ]
                    .into_iter()
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
                    if let Some(runtime) = build_core_c_runtime_library(&temp_dir.join("core_c_runtime")) {
                        candidates.push((runtime, false));
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
