//! Sysroot and runtime library discovery for cross-compilation.

use crate::target::Target;
use std::path::PathBuf;

/// Find the sysroot directory for a given target.
///
/// Searches in order:
/// 1. SIMPLE_SYSROOT environment variable
/// 2. /usr/local/lib/simple/{triple}/
/// 3. ~/.simple/sysroot/{triple}/
/// 4. Adjacent to compiler binary: ../lib/simple/{triple}/
pub fn find_sysroot(target: &Target) -> Option<PathBuf> {
    let triple = target.triple_str();

    // 1. Environment variable override
    if let Ok(sysroot) = std::env::var("SIMPLE_SYSROOT") {
        let path = PathBuf::from(sysroot);
        if path.exists() {
            return Some(path);
        }
    }

    // 2. System-wide installation
    let system_path = PathBuf::from(format!("/usr/local/lib/simple/{triple}"));
    if system_path.exists() {
        return Some(system_path);
    }

    // 3. User-local installation (uses USERPROFILE fallback on Windows)
    if let Some(home) = super::env::home() {
        let user_path = home.join(".simple").join("sysroot").join(triple);
        if user_path.exists() {
            return Some(user_path);
        }
    }

    // 4. Relative to compiler binary
    if let Ok(exe) = std::env::current_exe() {
        if let Some(bin_dir) = exe.parent() {
            let relative_path = bin_dir.join("..").join("lib").join("simple").join(triple);
            if relative_path.exists() {
                return Some(relative_path);
            }
        }
    }

    None
}

/// Find the runtime library file for a given target.
pub fn find_runtime_lib(target: &Target) -> Option<PathBuf> {
    let sysroot = find_sysroot(target)?;
    let ext = target.default_static_lib_ext();
    let lib_path = sysroot.join(format!("libsimple_runtime{ext}"));
    if lib_path.exists() {
        Some(lib_path)
    } else {
        None
    }
}
