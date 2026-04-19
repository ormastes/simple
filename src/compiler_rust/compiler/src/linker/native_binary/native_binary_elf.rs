//! ELF-specific platform helpers for native binary linking.
//!
//! Covers Linux and FreeBSD: library path detection, CRT startup files,
//! and dynamic linker path resolution.

use std::path::PathBuf;

use simple_common::target::{Target, TargetArch, TargetOS};

use super::super::error::{LinkerError, LinkerResult};

/// Detect library search paths for Linux targets.
pub fn linux_library_paths(target: &Target) -> Vec<PathBuf> {
    let arch_dirs: &[&str] = match target.arch {
        TargetArch::X86_64 => &[
            "/lib/x86_64-linux-gnu",
            "/usr/lib/x86_64-linux-gnu",
            "/lib64",
            "/usr/lib64",
            "/usr/lib/gcc/x86_64-linux-gnu/13",
            "/usr/lib/gcc/x86_64-linux-gnu/12",
            "/usr/lib/gcc/x86_64-linux-gnu/11",
        ],
        TargetArch::Aarch64 => &[
            "/lib/aarch64-linux-gnu",
            "/usr/lib/aarch64-linux-gnu",
            "/usr/aarch64-linux-gnu/lib",
        ],
        TargetArch::Riscv64 => &[
            "/lib/riscv64-linux-gnu",
            "/usr/lib/riscv64-linux-gnu",
            "/usr/riscv64-linux-gnu/lib",
        ],
        _ => &[],
    };

    let mut paths: Vec<PathBuf> = arch_dirs
        .iter()
        .map(|&p| PathBuf::from(p))
        .filter(|p| p.exists())
        .collect();

    for path in ["/lib", "/usr/lib"] {
        let p = PathBuf::from(path);
        if p.exists() {
            paths.push(p);
        }
    }
    paths
}

/// Detect library search paths for FreeBSD targets.
pub fn freebsd_library_paths() -> Vec<PathBuf> {
    ["/usr/lib", "/usr/local/lib"]
        .iter()
        .map(|&p| PathBuf::from(p))
        .filter(|p| p.exists())
        .collect()
}

/// Find CRT startup object files for Linux targets.
///
/// Returns `[crti.o, crt1.o/Scrt1.o, crtn.o]` in link order.
pub fn linux_crt_files(target: &Target, pie: bool, shared: bool) -> LinkerResult<Vec<PathBuf>> {
    let candidates: Vec<&str> = match target.arch {
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

    let mut crt_files = Vec::new();
    for dir in candidates {
        let dir_path = PathBuf::from(dir);
        let crt1 = if pie && !shared {
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

    if crt_files.is_empty() {
        let arch_name = format!("{:?}", target.arch).to_lowercase();
        return Err(LinkerError::LinkFailed(format!(
            "could not find C runtime startup files for {} (crt1.o, crti.o, crtn.o). \
             For cross-compilation, install the cross-toolchain (e.g., gcc-{}-linux-gnu)",
            arch_name, arch_name
        )));
    }
    Ok(crt_files)
}

/// Find CRT startup object files for FreeBSD targets.
pub fn freebsd_crt_files(target: &Target, pie: bool, shared: bool) -> LinkerResult<Vec<PathBuf>> {
    let dir_path = PathBuf::from("/usr/lib");
    let crt1 = if pie && !shared {
        dir_path.join("Scrt1.o")
    } else {
        dir_path.join("crt1.o")
    };
    let crti = dir_path.join("crti.o");
    let crtn = dir_path.join("crtn.o");

    let mut crt_files = Vec::new();
    if crt1.exists() && crti.exists() && crtn.exists() {
        crt_files.push(crti);
        crt_files.push(crt1);
        crt_files.push(crtn);
    }

    if crt_files.is_empty() {
        let arch_name = format!("{:?}", target.arch).to_lowercase();
        return Err(LinkerError::LinkFailed(format!(
            "could not find C runtime startup files for {} (crt1.o, crti.o, crtn.o). \
             For cross-compilation, install the cross-toolchain (e.g., gcc-{}-linux-gnu)",
            arch_name, arch_name
        )));
    }
    Ok(crt_files)
}

/// Resolve the dynamic linker path for Linux targets.
pub fn linux_dynamic_linker(target: &Target) -> Option<PathBuf> {
    let candidates: Vec<&str> = match target.arch {
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

    for path in &candidates {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }

    // Cross-compilation: return expected path even if not present locally.
    if target.arch != TargetArch::host() {
        return match target.arch {
            TargetArch::X86_64 => Some(PathBuf::from("/lib64/ld-linux-x86-64.so.2")),
            TargetArch::Aarch64 => Some(PathBuf::from("/lib/ld-linux-aarch64.so.1")),
            TargetArch::Riscv64 => Some(PathBuf::from("/lib/ld-linux-riscv64-lp64d.so.1")),
            _ => None,
        };
    }
    None
}

/// Resolve the dynamic linker path for FreeBSD targets.
pub fn freebsd_dynamic_linker(target: &Target) -> Option<PathBuf> {
    let p = PathBuf::from("/libexec/ld-elf.so.1");
    if p.exists() || target.arch != TargetArch::host() {
        Some(p)
    } else {
        None
    }
}
