//! C/C++ compiler detection.
//!
//! Consolidated logic for finding available C and C++ compilers,
//! previously duplicated in `native_project.rs` and `native_binary.rs`.

use crate::target::{LinkerFlavor, Target, TargetOS};

const WINDOWS_GNU_C_COMPILERS: &[&str] = &["gcc", "clang"];
const WINDOWS_GNU_CXX_COMPILERS: &[&str] = &["g++", "clang++"];
const MSVC_C_COMPILERS: &[&str] = &["clang-cl", "clang", "cl.exe"];
const MSVC_CXX_COMPILERS: &[&str] = &["clang-cl", "clang++", "clang"];

fn compiler_matches_flavor(compiler: &str, flavor: LinkerFlavor) -> bool {
    match flavor {
        LinkerFlavor::Msvc => is_msvc_target(compiler),
        LinkerFlavor::Gnu => !is_msvc_target(compiler),
        LinkerFlavor::WasmLd => true,
    }
}

fn cxx_candidates(target: &Target, flavor: LinkerFlavor) -> &'static [&'static str] {
    match (target.os, flavor) {
        (_, LinkerFlavor::Msvc) => MSVC_CXX_COMPILERS,
        (TargetOS::Windows, LinkerFlavor::Gnu) => WINDOWS_GNU_CXX_COMPILERS,
        _ => &["clang++", "g++"],
    }
}

/// Find a C compiler for the host platform.
///
/// Respects the `CC` environment variable. When `SIMPLE_LINKER_FLAVOR=msvc`,
/// prefers MSVC-compatible compilers (`clang-cl`). On Windows, prefers `clang-cl`.
/// On Unix, prefers `clang` over `gcc`.
pub fn find_c_compiler() -> String {
    detect_c_compiler_for_target(&Target::host())
}

/// Detect the C compiler for a specific target platform.
///
/// The target's resolved linker flavor selects an ABI-compatible toolchain:
/// Windows GNU prefers `gcc`; Windows MSVC prefers `clang-cl`.
/// On Unix targets, defaults to `cc`.
pub fn detect_c_compiler_for_target(target: &Target) -> String {
    if let Ok(cc) = std::env::var("CC") {
        return cc;
    }
    let flavor = target.linker_flavor();
    if flavor == LinkerFlavor::Msvc {
        for cc in MSVC_C_COMPILERS {
            if command_exists(cc) && compiler_matches_flavor(cc, flavor) {
                return cc.to_string();
            }
        }
        return "cl.exe".to_string();
    }
    match target.os {
        TargetOS::Windows => {
            for cc in WINDOWS_GNU_C_COMPILERS {
                if command_exists(cc) && compiler_matches_flavor(cc, flavor) {
                    return cc.to_string();
                }
            }
            "gcc".to_string()
        }
        _ if command_exists("clang") => "clang".to_string(),
        _ => "gcc".to_string(),
    }
}

/// Find a C++ compiler.
///
/// Uses the host target's resolved linker flavor. Windows GNU prefers `g++`;
/// Windows MSVC prefers `clang-cl`. On Unix, tries clang++ then g++.
pub fn find_cxx_compiler() -> String {
    detect_cxx_compiler_for_target(&Target::host())
}

/// Detect the C++ compiler for a specific target platform.
///
/// An explicit `CXX` chooses the executable, while the target's resolved
/// linker flavor determines the ABI-compatible automatic candidates.
pub fn detect_cxx_compiler_for_target(target: &Target) -> String {
    if let Ok(cxx) = std::env::var("CXX") {
        return cxx;
    }
    let flavor = target.linker_flavor();
    for cxx in cxx_candidates(target, flavor) {
        if command_exists(cxx) && compiler_matches_flavor(cxx, flavor) {
            return cxx.to_string();
        }
    }
    if flavor == LinkerFlavor::Msvc {
        "clang-cl".to_string()
    } else {
        "g++".to_string()
    }
}

/// Find an archive tool (ar, llvm-ar, or lib.exe on Windows).
pub fn find_archive_tool() -> String {
    if cfg!(target_os = "windows") {
        for tool in &["llvm-ar", "ar"] {
            if command_exists(tool) {
                return tool.to_string();
            }
        }
        // lib.exe: check via `where` since lib /? returns nonzero
        if let Ok(out) = std::process::Command::new("where").arg("lib").output() {
            if out.status.success() {
                return "lib".to_string();
            }
        }
        "ar".to_string()
    } else {
        // Prefer llvm-ar on macOS — it tolerates malformed Mach-O objects
        // that system ar/libtool/ranlib reject (Cranelift n_strx bug).
        for tool in &[
            "/opt/homebrew/opt/llvm@18/bin/llvm-ar",
            "/opt/homebrew/opt/llvm/bin/llvm-ar",
            "/usr/local/opt/llvm/bin/llvm-ar",
            "llvm-ar",
        ] {
            if command_exists(tool) {
                return tool.to_string();
            }
        }
        "ar".to_string()
    }
}

/// Find Homebrew LLVM lib directory for linking against its libc++.
/// Returns the lib path (e.g., "/opt/homebrew/opt/llvm@18/lib") if found.
pub fn find_homebrew_llvm_lib() -> Option<String> {
    if !cfg!(target_os = "macos") {
        return None;
    }
    let candidates = [
        "/opt/homebrew/opt/llvm@18/lib",
        "/opt/homebrew/opt/llvm/lib",
        "/usr/local/opt/llvm@18/lib",
        "/usr/local/opt/llvm/lib",
    ];
    for path in &candidates {
        let libc_path = format!("{}/libc++.dylib", path);
        if std::path::Path::new(&libc_path).exists() {
            return Some(path.to_string());
        }
    }
    None
}

/// Check if a compiler name looks like MSVC cl.exe.
pub fn is_msvc_compiler(cc: &str) -> bool {
    let base = std::path::Path::new(cc)
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(cc);
    base.eq_ignore_ascii_case("cl") || base.eq_ignore_ascii_case("cl.exe")
}

/// Check if a C/C++ compiler targets the MSVC ABI.
///
/// Returns true for clang-cl, cl.exe, or any clang whose default target
/// triple contains "windows-msvc". This determines whether to use
/// MSVC-style linker flags (/WHOLEARCHIVE, /FORCE:UNRESOLVED) or
/// GNU-style (-Wl,--whole-archive, etc.).
pub fn is_msvc_target(cc: &str) -> bool {
    let base = std::path::Path::new(cc)
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(cc);
    // clang-cl and cl.exe always target MSVC
    if base.contains("clang-cl") || is_msvc_compiler(cc) {
        return true;
    }
    // For plain clang/clang++, check the effective target triple
    if base.starts_with("clang") {
        if let Ok(output) = std::process::Command::new(cc).arg("--print-effective-triple").output() {
            let triple = String::from_utf8_lossy(&output.stdout);
            return triple.contains("windows-msvc");
        }
    }
    false
}

/// Check if the `SIMPLE_LINKER_FLAVOR` env var is set to "msvc".
///
/// When true, compiler detection should prefer MSVC-compatible tools
/// (`clang-cl`, `lld-link`) over MinGW tools (`gcc`, `g++`, `ld`).
pub fn is_msvc_linker_flavor() -> bool {
    std::env::var("SIMPLE_LINKER_FLAVOR").is_ok_and(|v| v.eq_ignore_ascii_case("msvc"))
}

/// Check if a command exists and works by running `--version`.
///
/// Verifies both that the process can be spawned AND that it exits
/// successfully (exit code 0). This catches cases like a clang++
/// that exists on PATH but crashes due to missing shared libraries.
pub fn command_exists(name: &str) -> bool {
    std::process::Command::new(name)
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::target::TargetArch;

    #[test]
    fn windows_gnu_prefers_gnu_compilers() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Windows);
        assert_eq!(WINDOWS_GNU_C_COMPILERS, &["gcc", "clang"]);
        assert_eq!(cxx_candidates(&target, LinkerFlavor::Gnu), &["g++", "clang++"]);
        assert!(!compiler_matches_flavor("clang-cl", LinkerFlavor::Gnu));
    }

    #[test]
    fn windows_msvc_keeps_msvc_compilers() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Windows);
        assert_eq!(MSVC_C_COMPILERS, &["clang-cl", "clang", "cl.exe"]);
        assert_eq!(
            cxx_candidates(&target, LinkerFlavor::Msvc),
            &["clang-cl", "clang++", "clang"]
        );
        assert!(compiler_matches_flavor("clang-cl", LinkerFlavor::Msvc));
    }
}
