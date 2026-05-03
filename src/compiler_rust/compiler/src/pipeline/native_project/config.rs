//! Build configuration: runtime bundle selection, runtime library discovery.

use std::path::{Path, PathBuf};

use super::NativeProjectBuilder;
use super::tools::strip_llvm_constructors;
use super::tools::{find_native_all_library, find_runtime_library};

fn runtime_bundle_requests_core_c(value: &str) -> bool {
    matches!(value, "runtime" | "core" | "core-c" | "core_c")
}

fn runtime_bundle_requests_hosted(value: &str) -> bool {
    matches!(value, "all" | "hosted" | "rust-hosted")
}

impl NativeProjectBuilder {
    pub(crate) fn runtime_bundle_prefers_core_c_lane(&self) -> bool {
        match self.config.runtime_bundle.as_str() {
            value if runtime_bundle_requests_core_c(value) => return true,
            value if runtime_bundle_requests_hosted(value) => return false,
            _ => {}
        }
        if std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_core_c)
        {
            return true;
        }
        if std::env::var("SIMPLE_NATIVE_RUNTIME_BUNDLE")
            .ok()
            .as_deref()
            .is_some_and(runtime_bundle_requests_hosted)
        {
            return false;
        }
        let compiler_like = |path: &Path| {
            let p = path.to_string_lossy().replace('\\', "/");
            p.contains("/src/compiler/")
                || p.ends_with("/src/compiler")
                || p.contains("/src/app/cli/")
                || p.ends_with("/src/app/cli")
        };
        if self.entry_file.as_ref().is_some_and(|p| compiler_like(p)) {
            return false;
        }
        if self.source_dirs.iter().any(|p| compiler_like(p)) {
            return false;
        }
        true
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

    pub(crate) fn reject_unexpected_native_all(
        &self,
        selected_runtime: Option<&(PathBuf, bool)>,
    ) -> Result<(), String> {
        if self.runtime_bundle_is_explicit_hosted() || !self.runtime_bundle_prefers_core_c_lane() {
            return Ok(());
        }
        if let Some((runtime_lib, true)) = selected_runtime {
            let entry = self
                .entry_file
                .as_ref()
                .map(|path| path.display().to_string())
                .unwrap_or_else(|| "<none>".to_string());
            return Err(format!(
                "native-build refused rust-hosted runtime for default core-c entry `{}`: selected `{}`. Provide libsimple_runtime.a for the core-c lane or pass `--runtime-bundle hosted` (legacy: `all`) to opt into the hosted lane explicitly.",
                entry,
                runtime_lib.display()
            ));
        }
        Ok(())
    }

    pub(crate) fn selected_runtime_library(&self, temp_dir: &Path) -> Option<(PathBuf, bool)> {
        let prefer_core_c_lane = self.runtime_bundle_prefers_core_c_lane();
        let mut candidates: Vec<(PathBuf, bool)> = Vec::new();

        let mut push_runtime_candidates = |dir: &Path| {
            let runtime = dir.join("libsimple_runtime.a");
            let native_all = dir.join("libsimple_native_all.a");
            if prefer_core_c_lane {
                if runtime.exists() {
                    candidates.push((runtime, false));
                }
                if native_all.exists() {
                    // LIM-010: Always strip LLVM constructors from native_all to prevent
                    // segfaults from ManagedStatic initialization (not just in bootstrap mode).
                    let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                    candidates.push((lib, true));
                }
            } else {
                if native_all.exists() {
                    let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                    candidates.push((lib, true));
                }
                if runtime.exists() {
                    candidates.push((runtime, false));
                }
            }
        };

        if let Some(ref rp) = self.config.runtime_path {
            push_runtime_candidates(rp);
        } else {
            if let Some(runtime) = find_runtime_library() {
                if prefer_core_c_lane {
                    candidates.push((runtime, false));
                }
            }
            if let Some(native_all) = find_native_all_library() {
                let lib = strip_llvm_constructors(&native_all, temp_dir).unwrap_or(native_all.clone());
                if prefer_core_c_lane {
                    if !candidates.iter().any(|(p, _)| p == &lib) {
                        candidates.push((lib, true));
                    }
                } else {
                    candidates.insert(0, (lib, true));
                }
            }
            if !prefer_core_c_lane {
                if let Some(runtime) = find_runtime_library() {
                    if !candidates.iter().any(|(p, _)| p == &runtime) {
                        candidates.push((runtime, false));
                    }
                }
            }
        }
        candidates.into_iter().next()
    }
}
