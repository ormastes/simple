use std::path::{Path, PathBuf};

use object::{Object, ObjectSymbol};
use simple_common::target::{LinkerFlavor, TargetOS};

use crate::linker::builder::LinkerBuilder;
use crate::linker::error::{LinkerError, LinkerResult};

use super::builder::NativeBinaryBuilder;
use super::options::NativeBinaryOptions;
use super::stubs::ALLOW_UNRESOLVED_RT_ENV;

impl NativeBinaryBuilder {
    /// Post-link safety net for task #97: parse the final linked artifact in-process (via the
    /// `object` crate) and check whether any `rt_*` symbol is still genuinely undefined. Under
    /// normal bootstrap-mode builds the auto-stub generator (see stubs.rs) already fabricates a
    /// definition for every undefined symbol before this point, so this scan is expected to find
    /// nothing there — it exists to catch the non-bootstrap / shared-library link paths (which
    /// don't run the auto-stub passes) where `--unresolved-symbols=ignore-all` or a lenient
    /// dynamic linker could otherwise let a real undefined `rt_*` symbol ship silently.
    pub(super) fn verify_no_undefined_rt_symbols(&self, output_path: &Path) -> LinkerResult<()> {
        let data = match std::fs::read(output_path) {
            Ok(d) => d,
            Err(_) => return Ok(()), // nothing to verify
        };
        let obj = match object::File::parse(&*data) {
            Ok(o) => o,
            Err(_) => return Ok(()), // not an object/executable we can parse (e.g. PE quirks) — skip
        };
        let mut undefined_rt: Vec<String> = obj
            .symbols()
            .filter(|sym| sym.is_undefined())
            .filter_map(|sym| sym.name().ok().map(|n| n.to_string()))
            .filter(|name| name.starts_with("rt_"))
            .collect();
        undefined_rt.sort();
        undefined_rt.dedup();
        if undefined_rt.is_empty() {
            return Ok(());
        }
        let names = undefined_rt.join(", ");
        if std::env::var(ALLOW_UNRESOLVED_RT_ENV).as_deref() == Ok("1") {
            eprintln!(
                "WARNING (task #97): linked artifact {} still has genuinely undefined rt_* \
                 symbol(s) [{names}] ({env}=1 set — proceeding anyway). These will crash at call \
                 time.",
                output_path.display(),
                names = names,
                env = ALLOW_UNRESOLVED_RT_ENV,
            );
            return Ok(());
        }
        Err(LinkerError::LinkFailed(format!(
            "native-build: linked artifact {} has genuinely undefined rt_* symbol(s) [{names}] \
             (task #97) — calling them would jump to address 0. Fix the extern name/declaration, \
             implement it in the runtime, or set {env}=1 to bypass at your own risk.",
            output_path.display(),
            names = names,
            env = ALLOW_UNRESOLVED_RT_ENV,
        )))
    }

    pub(super) fn object_has_undefined_symbols(&self, obj_path: &Path) -> bool {
        let (nm_cmd, nm_args) = super::options::detect_nm_command(&self.options.target);
        std::process::Command::new(nm_cmd)
            .args(nm_args)
            .arg(obj_path)
            .output()
            .map(|out| out.status.success() && !String::from_utf8_lossy(&out.stdout).trim().is_empty())
            .unwrap_or(true)
    }

    fn runtime_free_libraries(&self) -> Vec<String> {
        match self.options.target.os {
            TargetOS::Linux | TargetOS::FreeBSD => vec!["c".to_string()],
            TargetOS::MacOS => vec!["System".to_string()],
            TargetOS::Windows => vec!["c".to_string(), "msvcrt".to_string(), "kernel32".to_string()],
            _ => vec!["c".to_string()],
        }
    }

    /// Execute one link pass.
    ///
    /// `out_path` — output file path.
    /// `allow_unresolved` — pass --unresolved-symbols=ignore-all (pass 1).
    /// `extra_stubs` — bootstrap stub objects to include via --whole-archive.
    /// `require_crypto` — add -lcrypto.
    /// `crt_files` — CRT startup objects (crti, crt1/Scrt1, crtn).
    pub(super) fn run_link_pass(
        &self,
        out_path: &Path,
        allow_unresolved: bool,
        extra_stubs: &[PathBuf],
        require_crypto: bool,
        obj_path: &Path,
        crt_files: &[PathBuf],
    ) -> LinkerResult<()> {
        let linker_flavor = self.options.target.linker_flavor();
        let mut builder = LinkerBuilder::new().target(self.options.target);

        let runtime_free_object = !self.object_has_undefined_symbols(obj_path);

        if !runtime_free_object && crt_files.len() >= 2 {
            builder = builder.object(&crt_files[0]);
            builder = builder.object(&crt_files[1]);
        }

        builder = builder.object(obj_path);

        let runtime_dir =
            NativeBinaryOptions::find_runtime_library_path_for_target(&self.options.target).or_else(|| {
                if self.options.target == simple_common::target::Target::host() {
                    std::env::current_dir()
                        .ok()
                        .map(|p| p.join("target/debug"))
                        .filter(|p| p.join("libsimple_runtime.a").exists())
                } else {
                    None
                }
            });

        let has_named_runtime_root = self
            .options
            .libraries
            .iter()
            .any(|lib| matches!(lib.as_str(), "simple_runtime" | "simple_native_all" | "simple_compiler"));

        if !runtime_free_object && !has_named_runtime_root {
            if let Some(runtime_dir) = runtime_dir.as_ref() {
                let runtime_lib = runtime_dir.join("libsimple_runtime.a");
                let compiler_lib = runtime_dir.join("libsimple_compiler.a");
                if runtime_lib.exists() {
                    builder = builder.object(&runtime_lib);
                } else if compiler_lib.exists() {
                    builder = builder.object(&compiler_lib);
                }
            }
        }

        if !extra_stubs.is_empty()
            && runtime_dir.is_some()
            && linker_flavor == LinkerFlavor::Gnu
            && !matches!(self.options.target.os, TargetOS::MacOS)
        {
            builder = builder.flag("--allow-multiple-definition".to_string());
        }

        if !extra_stubs.is_empty() {
            match linker_flavor {
                LinkerFlavor::Msvc => {
                    for stub in extra_stubs {
                        builder = builder.flag(format!("/WHOLEARCHIVE:{}", stub.display()));
                    }
                }
                LinkerFlavor::Gnu => {
                    if matches!(self.options.target.os, TargetOS::MacOS) {
                        for stub in extra_stubs {
                            builder = builder.flag("-force_load".to_string());
                            builder = builder.flag(stub.display().to_string());
                        }
                    } else {
                        builder = builder.flag("--whole-archive");
                        for stub in extra_stubs {
                            builder = builder.object(stub);
                        }
                        builder = builder.flag("--no-whole-archive");
                    }
                }
                LinkerFlavor::WasmLd => {
                    builder = builder.flag("--whole-archive");
                    for stub in extra_stubs {
                        builder = builder.object(stub);
                    }
                    builder = builder.flag("--no-whole-archive");
                }
            }
        }

        if allow_unresolved {
            match linker_flavor {
                LinkerFlavor::Msvc => {
                    builder = builder.flag("/FORCE:UNRESOLVED".to_string());
                }
                LinkerFlavor::Gnu => {
                    if matches!(self.options.target.os, TargetOS::MacOS) {
                        builder = builder.flag("-undefined".to_string());
                        builder = builder.flag("dynamic_lookup".to_string());
                    } else {
                        builder = builder.flag("--unresolved-symbols=ignore-all".to_string());
                    }
                }
                LinkerFlavor::WasmLd => {
                    builder = builder.flag("--allow-undefined".to_string());
                }
            }
        }

        builder = builder.output(out_path);

        if let Some(linker) = self.options.linker {
            builder = builder.linker(linker);
        }
        let runtime_free_libraries;
        let libraries = if runtime_free_object && !self.options.shared {
            runtime_free_libraries = Vec::new();
            &runtime_free_libraries
        } else {
            &self.options.libraries
        };
        for lib in libraries {
            builder = builder.library(lib);
        }
        let runtime_free_library_paths;
        let library_paths = if runtime_free_object && !self.options.shared {
            runtime_free_library_paths = self
                .options
                .library_paths
                .iter()
                .filter(|path| {
                    let s = path.to_string_lossy();
                    !s.contains("compiler_rust/target") && !path.join("libsimple_runtime.a").exists()
                })
                .cloned()
                .collect::<Vec<_>>();
            &runtime_free_library_paths
        } else {
            &self.options.library_paths
        };
        for path in library_paths {
            builder = builder.library_path(path);
        }
        if require_crypto {
            builder = builder.library("crypto");
        }
        let effective_pie = self.options.pie && !runtime_free_object;

        if self.options.strip {
            builder = builder.strip();
        }
        if self.options.shared {
            builder = builder.shared();
        } else if effective_pie {
            builder = builder.pie();
        }
        if self.options.generate_map {
            builder = builder.auto_map();
        }
        if self.options.verbose {
            builder = builder.verbose();
        }

        if !self.options.shared
            && matches!(linker_flavor, LinkerFlavor::Gnu)
            && !matches!(self.options.target.os, TargetOS::MacOS)
        {
            if !runtime_free_object {
                if let Some(dynamic_linker) = self.find_dynamic_linker() {
                    builder = builder.flag(format!("--dynamic-linker={}", dynamic_linker.display()));
                }
            }
            if !effective_pie {
                builder = builder.flag("-no-pie".to_string());
            }
        }

        if !runtime_free_object && crt_files.len() >= 3 {
            builder = builder.object(&crt_files[2]);
        }

        builder.link()
    }
}
