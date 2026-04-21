use std::path::{Path, PathBuf};
use std::process::Command;

use simple_common::target::TargetOS;

use crate::linker::error::{LinkerError, LinkerResult};
use crate::linker::layout::LayoutOptimizer;

use super::options::{NativeBinaryOptions, asm_ret_instruction};
use super::result::NativeBinaryResult;

/// Builder for native binaries.
#[derive(Debug)]
pub struct NativeBinaryBuilder {
    pub(super) object_code: Vec<u8>,
    pub options: NativeBinaryOptions,
    pub(super) layout_optimizer: Option<LayoutOptimizer>,
}

impl NativeBinaryBuilder {
    pub fn new(object_code: Vec<u8>) -> Self {
        Self {
            object_code,
            options: NativeBinaryOptions::default(),
            layout_optimizer: None,
        }
    }

    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.options.output = path.into();
        self
    }

    impl_target_method!(options);
    impl_layout_methods!(options);
    impl_bool_flag_methods!(options);
    impl_linker_builder_methods!(options);
    impl_linker_method!(options);

    pub fn options(mut self, options: NativeBinaryOptions) -> Self {
        self.options = options;
        self
    }

    pub fn with_layout_optimizer(mut self, optimizer: LayoutOptimizer) -> Self {
        self.layout_optimizer = Some(optimizer);
        self
    }

    pub fn build(self) -> LinkerResult<NativeBinaryResult> {
        let temp_dir =
            tempfile::tempdir().map_err(|e| LinkerError::LinkFailed(format!("failed to create temp dir: {}", e)))?;
        let (temp_path, _temp_guard) = if std::env::var("SIMPLE_KEEP_TEMP").is_ok() {
            let path = temp_dir.keep();
            eprintln!("SIMPLE_KEEP_TEMP=1: keeping temp objects in {}", path.display());
            (path, None)
        } else {
            (temp_dir.path().to_path_buf(), Some(temp_dir))
        };

        let obj_path = temp_path.join("main.o");
        std::fs::write(&obj_path, &self.object_code)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write object file: {}", e)))?;

        let mut bootstrap_stubs: Vec<PathBuf> = Vec::new();
        let bootstrap_mode = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1")
            || matches!(self.options.target.os, TargetOS::FreeBSD);
        let require_crypto = false;
        let ret_insn = asm_ret_instruction(&self.options.target);

        if !self.options.shared {
            self.build_main_shim(&temp_path, &mut bootstrap_stubs)?;
        }

        if bootstrap_mode {
            self.build_pass1_stubs(&temp_path, &obj_path, ret_insn, &mut bootstrap_stubs)?;
        }

        if self.options.verbose || std::env::var("SIMPLE_LINKER_DEBUG").is_ok() {
            eprintln!("Object file: {}", obj_path.display());
            if let Ok(output) = Command::new("nm").arg(&obj_path).output() {
                eprintln!("Symbols in object file:");
                eprintln!("{}", String::from_utf8_lossy(&output.stdout));
            }
        }

        let crt_files = if self.options.shared {
            Vec::new()
        } else {
            self.find_crt_files()?
        };

        let _ordering_file = if self.options.layout_optimize {
            self.generate_ordering_file(&temp_path)?
        } else {
            None
        };

        let temp_out = temp_path.join("_bootstrap_pass1");
        let first_out: &Path = if bootstrap_mode {
            &temp_out
        } else {
            Path::new(&self.options.output)
        };
        self.run_link_pass(
            first_out,
            bootstrap_mode,
            &bootstrap_stubs,
            require_crypto,
            &obj_path,
            &crt_files,
        )?;

        let final_result = if bootstrap_mode {
            self.build_pass2_stubs(&temp_path, first_out, ret_insn, &mut bootstrap_stubs)?;
            self.run_link_pass(
                Path::new(&self.options.output),
                false,
                &bootstrap_stubs,
                require_crypto,
                &obj_path,
                &crt_files,
            )
        } else {
            Ok(())
        };

        match final_result {
            Ok(()) => Ok(NativeBinaryResult {
                output: self.options.output.clone(),
                size: std::fs::metadata(&self.options.output).map(|m| m.len()).unwrap_or(0),
            }),
            Err(LinkerError::LinkerFailed {
                exit_code,
                message,
                stderr,
            }) => {
                eprintln!("Linker error (exit code {}): {}", exit_code, message);
                if !stderr.is_empty() {
                    eprintln!("Linker stderr:\n{}", stderr);
                }
                Err(LinkerError::LinkFailed(format!(
                    "{}: {}",
                    message,
                    stderr.lines().next().unwrap_or("")
                )))
            }
            Err(e) => Err(e),
        }
    }
}
