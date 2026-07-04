use std::io::Write;
use std::path::{Path, PathBuf};

use simple_common::target::{TargetArch, TargetOS};

use crate::linker::error::{LinkerError, LinkerResult};
use crate::linker::layout::LayoutOptimizer;

use super::builder::NativeBinaryBuilder;

impl NativeBinaryBuilder {
    /// Find C runtime startup files on the system.
    ///
    /// Linux/FreeBSD: crt1.o/Scrt1.o, crti.o, crtn.o.
    /// macOS/Windows: returns empty (CRT handled by toolchain).
    pub(super) fn find_crt_files(&self) -> LinkerResult<Vec<PathBuf>> {
        let mut crt_files = Vec::new();

        match self.options.target.os {
            TargetOS::Linux => {
                let candidates: Vec<&str> = match self.options.target.arch {
                    TargetArch::X86_64 => vec![
                        "/usr/lib/x86_64-linux-gnu",
                        "/usr/lib64",
                        "/lib/x86_64-linux-gnu",
                        "/lib64",
                    ],
                    TargetArch::Aarch64 => vec![
                        "/usr/lib/aarch64-linux-gnu",
                        "/usr/aarch64-linux-gnu/lib",
                        "/lib/aarch64-linux-gnu",
                    ],
                    TargetArch::Riscv64 => vec![
                        "/usr/lib/riscv64-linux-gnu",
                        "/usr/riscv64-linux-gnu/lib",
                        "/lib/riscv64-linux-gnu",
                    ],
                    _ => vec!["/usr/lib"],
                };

                for dir in candidates {
                    let dir_path = PathBuf::from(dir);
                    let crt1 = if self.options.pie && !self.options.shared {
                        dir_path.join("Scrt1.o")
                    } else {
                        dir_path.join("crt1.o")
                    };
                    let crti = dir_path.join("crti.o");
                    let crtn = dir_path.join("crtn.o");

                    if crt1.exists() && crti.exists() && crtn.exists() {
                        crt_files.push(crti);
                        crt_files.push(crt1);
                        crt_files.push(crtn);
                        break;
                    }
                }
            }
            TargetOS::FreeBSD => {
                let dir_path = PathBuf::from("/usr/lib");
                let crt1 = if self.options.pie && !self.options.shared {
                    dir_path.join("Scrt1.o")
                } else {
                    dir_path.join("crt1.o")
                };
                let crti = dir_path.join("crti.o");
                let crtn = dir_path.join("crtn.o");

                if crt1.exists() && crti.exists() && crtn.exists() {
                    crt_files.push(crti);
                    crt_files.push(crt1);
                    crt_files.push(crtn);
                }
            }
            TargetOS::MacOS => return Ok(crt_files),
            TargetOS::Windows => return Ok(crt_files),
            _ => return Ok(crt_files),
        }

        if crt_files.is_empty() && matches!(self.options.target.os, TargetOS::Linux | TargetOS::FreeBSD) {
            let arch_name = format!("{:?}", self.options.target.arch).to_lowercase();
            return Err(LinkerError::LinkFailed(format!(
                "could not find C runtime startup files for {} (crt1.o, crti.o, crtn.o). \
                 For cross-compilation, install the cross-toolchain (e.g., gcc-{}-linux-gnu)",
                arch_name, arch_name
            )));
        }

        Ok(crt_files)
    }

    /// Find the dynamic linker path for the target system.
    ///
    /// Linux: architecture-specific ld-linux paths.
    /// FreeBSD: /libexec/ld-elf.so.1.
    /// macOS/Windows: None.
    pub(super) fn find_dynamic_linker(&self) -> Option<PathBuf> {
        match self.options.target.os {
            TargetOS::Linux => {
                let candidates: Vec<&str> = match self.options.target.arch {
                    TargetArch::X86_64 => vec![
                        "/lib64/ld-linux-x86-64.so.2",
                        "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
                        "/lib/ld-linux-x86-64.so.2",
                    ],
                    TargetArch::Aarch64 => vec![
                        "/lib/ld-linux-aarch64.so.1",
                        "/lib/aarch64-linux-gnu/ld-linux-aarch64.so.1",
                    ],
                    TargetArch::Riscv64 => vec![
                        "/lib/ld-linux-riscv64-lp64d.so.1",
                        "/lib/riscv64-linux-gnu/ld-linux-riscv64-lp64d.so.1",
                    ],
                    _ => vec![],
                };

                for path in candidates {
                    let p = PathBuf::from(path);
                    if p.exists() {
                        return Some(p);
                    }
                }

                if self.options.target.arch != TargetArch::host() {
                    return match self.options.target.arch {
                        TargetArch::X86_64 => Some(PathBuf::from("/lib64/ld-linux-x86-64.so.2")),
                        TargetArch::Aarch64 => Some(PathBuf::from("/lib/ld-linux-aarch64.so.1")),
                        TargetArch::Riscv64 => Some(PathBuf::from("/lib/ld-linux-riscv64-lp64d.so.1")),
                        _ => None,
                    };
                }

                None
            }
            TargetOS::FreeBSD => {
                let p = PathBuf::from("/libexec/ld-elf.so.1");
                if p.exists() || self.options.target.arch != TargetArch::host() {
                    Some(p)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Generate symbol ordering file for layout optimization.
    pub(super) fn generate_ordering_file(&self, temp_dir: &Path) -> LinkerResult<Option<PathBuf>> {
        let optimizer = match &self.layout_optimizer {
            Some(opt) => opt,
            None => return Ok(None),
        };

        let symbols = optimizer.get_ordered_symbols();
        if symbols.is_empty() {
            return Ok(None);
        }

        let ordering_path = temp_dir.join("symbol_order.txt");
        let mut file = std::fs::File::create(&ordering_path)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to create ordering file: {}", e)))?;

        for symbol in symbols {
            writeln!(file, "{}", symbol)
                .map_err(|e| LinkerError::LinkFailed(format!("failed to write symbol: {}", e)))?;
        }

        Ok(Some(ordering_path))
    }
}
