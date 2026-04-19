use std::path::{Path, PathBuf};

use simple_common::target::{LinkerFlavor, TargetOS};

use crate::linker::builder::LinkerBuilder;
use crate::linker::error::{LinkerError, LinkerResult};

use super::builder::NativeBinaryBuilder;
use super::options::NativeBinaryOptions;

impl NativeBinaryBuilder {
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

        if crt_files.len() >= 2 {
            builder = builder.object(&crt_files[0]);
            builder = builder.object(&crt_files[1]);
        }

        builder = builder.object(obj_path);

        let runtime_dir = NativeBinaryOptions::find_runtime_library_path().or_else(|| {
            std::env::current_dir()
                .ok()
                .map(|p| p.join("target/debug"))
                .filter(|p| p.join("libsimple_runtime.a").exists())
        });

        if let Some(runtime_dir) = &runtime_dir {
            let runtime_lib = runtime_dir.join("libsimple_runtime.a");
            let compiler_lib = runtime_dir.join("libsimple_compiler.a");
            if runtime_lib.exists() {
                builder = builder.object(&runtime_lib);
            } else if compiler_lib.exists() {
                builder = builder.object(&compiler_lib);
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
        for lib in &self.options.libraries {
            builder = builder.library(lib);
        }
        for path in &self.options.library_paths {
            builder = builder.library_path(path);
        }
        if require_crypto {
            builder = builder.library("crypto");
        }
        if self.options.strip {
            builder = builder.strip();
        }
        if self.options.shared {
            builder = builder.shared();
        } else if self.options.pie {
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
            if let Some(dynamic_linker) = self.find_dynamic_linker() {
                builder = builder.flag(format!("--dynamic-linker={}", dynamic_linker.display()));
            }
            if !self.options.pie {
                builder = builder.flag("-no-pie".to_string());
            }
        }

        if crt_files.len() >= 3 {
            builder = builder.object(&crt_files[2]);
        }

        builder.link()
    }
}
