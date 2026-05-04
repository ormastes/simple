//! Build configuration: runtime bundle selection, runtime library discovery.

use std::path::{Path, PathBuf};

use super::tools::strip_llvm_constructors;
use super::tools::{
    build_core_c_runtime_library, find_native_all_library, find_runtime_library, find_simple_core_runtime_library,
};
use super::NativeProjectBuilder;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum NativeRuntimeLane {
    SimpleCore,
    CoreCBootstrap,
    RustHosted,
}

impl NativeRuntimeLane {
    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::SimpleCore => "simple-core",
            Self::CoreCBootstrap => "core-c-bootstrap",
            Self::RustHosted => "rust-hosted",
        }
    }
}

fn runtime_bundle_requests_simple_core(value: &str) -> bool {
    matches!(value, "simple-core" | "simple_core")
}

fn runtime_bundle_requests_core_c_bootstrap(value: &str) -> bool {
    matches!(value, "core-c-bootstrap" | "core_c_bootstrap" | "runtime" | "core" | "core-c" | "core_c")
}

fn runtime_bundle_requests_hosted(value: &str) -> bool {
    matches!(value, "all" | "hosted" | "rust-hosted")
}

fn is_compiler_like_entry(path: &Path) -> bool {
    let p = path.to_string_lossy().replace('\\', "/");
    p.contains("/src/compiler/")
        || p.ends_with("/src/compiler")
        || p.contains("/src/app/cli/")
        || p.ends_with("/src/app/cli")
}

fn runtime_path_has_simple_core(runtime_path: Option<&Path>) -> bool {
    runtime_path.is_some_and(|path| {
        ["simple-core", "simple_core"].iter().any(|lane_dir| {
            let dir = path.join(lane_dir);
            dir.join("libsimple_runtime.a").exists() || dir.join("deps").join("libsimple_runtime.a").exists()
        })
    })
}

impl NativeProjectBuilder {
    pub(crate) fn runtime_bundle_prefers_core_lane(&self) -> bool {
        !matches!(self.resolve_runtime_lane(), NativeRuntimeLane::RustHosted)
    }

    pub(crate) fn resolve_runtime_lane(&self) -> NativeRuntimeLane {
        match self.config.runtime_bundle.as_str() {
            value if runtime_bundle_requests_simple_core(value) => return NativeRuntimeLane::SimpleCore,
            value if runtime_bundle_requests_core_c_bootstrap(value) => return NativeRuntimeLane::CoreCBootstrap,
            value if runtime_bundle_requests_hosted(value) => return NativeRuntimeLane::RustHosted,
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
        if std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_hosted)
        {
            return NativeRuntimeLane::RustHosted;
        }
        if let Some(entry_file) = self.entry_file.as_ref() {
            if is_compiler_like_entry(entry_file) {
                return NativeRuntimeLane::RustHosted;
            }
        } else if self.source_dirs.iter().any(|p| is_compiler_like_entry(p)) {
            return NativeRuntimeLane::RustHosted;
        }
        if runtime_path_has_simple_core(self.config.runtime_path.as_deref()) || find_simple_core_runtime_library().is_some()
        {
            NativeRuntimeLane::SimpleCore
        } else {
            NativeRuntimeLane::CoreCBootstrap
        }
    }

    pub(crate) fn runtime_bundle_is_explicit_hosted(&self) -> bool {
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
        if self.runtime_bundle_is_explicit_hosted() || !self.runtime_bundle_prefers_core_lane() {
            return Ok(());
        }
        if let Some((runtime_lib, true)) = selected_runtime {
            let entry = self
                .entry_file
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "<none>".to_string());
            return Err(format!(
                "native-build refused rust-hosted runtime for `{}` on the `{}` lane: selected `{}`. Provide a core-lane libsimple_runtime.a archive for that lane or pass `--runtime-bundle rust-hosted` (legacy: `hosted`/`all`) to opt into the hosted lane explicitly.",
                entry,
                self.resolve_runtime_lane().display_name(),
                runtime_lib.display()
            ));
        }
        Ok(())
    }

    pub(crate) fn selected_runtime_library(&self, temp_dir: &Path) -> Result<Option<(PathBuf, bool)>, String> {
        let lane = self.resolve_runtime_lane();
        let mut candidates: Vec<(PathBuf, bool)> = Vec::new();

        let mut push_runtime_candidates = |dir: &Path| {
            let runtime_deps = dir.join("deps").join("libsimple_runtime.a");
            let runtime = dir.join("libsimple_runtime.a");
            let native_all = dir.join("libsimple_native_all.a");
            match lane {
                NativeRuntimeLane::CoreCBootstrap => {
                    if runtime_deps.exists() {
                        candidates.push((runtime_deps, false));
                    }
                    if runtime.exists() {
                        candidates.push((runtime, false));
                    }
                    if native_all.exists() {
                        let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                        candidates.push((lib, true));
                    }
                }
                NativeRuntimeLane::SimpleCore => {
                    for lane_dir in ["simple-core", "simple_core"] {
                        let candidate_dir = dir.join(lane_dir);
                        let lane_runtime_deps = candidate_dir.join("deps").join("libsimple_runtime.a");
                        let lane_runtime = candidate_dir.join("libsimple_runtime.a");
                        if lane_runtime_deps.exists() {
                            candidates.push((lane_runtime_deps, false));
                        }
                        if lane_runtime.exists() {
                            candidates.push((lane_runtime, false));
                        }
                    }
                }
                NativeRuntimeLane::RustHosted => {
                    if native_all.exists() {
                        let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                        candidates.push((lib, true));
                    }
                }
            }
        };

        if let Some(ref rp) = self.config.runtime_path {
            push_runtime_candidates(rp);
        } else {
            match lane {
                NativeRuntimeLane::SimpleCore => {
                    if let Some(runtime) = find_simple_core_runtime_library() {
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
                    if let Some(native_all) = find_native_all_library() {
                        let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                        if !candidates.iter().any(|(p, _)| p == &lib) {
                            candidates.push((lib, true));
                        }
                    }
                }
                NativeRuntimeLane::RustHosted => {
                    if let Some(native_all) = find_native_all_library() {
                        let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                        candidates.push((lib, true));
                    }
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
