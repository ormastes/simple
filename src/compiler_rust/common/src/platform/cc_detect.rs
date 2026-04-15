//! C/C++ compiler detection.
//!
//! Consolidated logic for finding available C and C++ compilers,
//! previously duplicated in `native_project.rs` and `native_binary.rs`.

use crate::target::{Target, TargetOS};

/// Find a C compiler for the host platform.
///
/// Respects the `CC` environment variable. When `SIMPLE_LINKER_FLAVOR=msvc`,
/// prefers MSVC-compatible compilers (`clang-cl`). On Windows, prefers `clang-cl`.
/// On Unix, prefers `clang` over `gcc`.
pub fn find_c_compiler() -> String {
    if let Ok(cc) = std::env::var("CC") {
        return cc;
    }

    // When SIMPLE_LINKER_FLAVOR=msvc, prefer MSVC-compatible compilers
    // to ensure the linker driver invokes lld-link (not MinGW ld).
    if is_msvc_linker_flavor() {
        for cc in &["clang-cl", "clang", "cl.exe"] {
            if command_exists(cc) && is_msvc_target(cc) {
                return cc.to_string();
            }
        }
    }

    if cfg!(target_os = "windows") {
        for cc in &["clang-cl", "clang", "gcc"] {
            if command_exists(cc) {
                return cc.to_string();
            }
        }
        "clang".to_string()
    } else if command_exists("clang") {
        "clang".to_string()
    } else {
        "gcc".to_string()
    }
}

/// Detect the C compiler for a specific target platform.
///
/// When `SIMPLE_LINKER_FLAVOR=msvc`, prefers `clang-cl` to ensure
/// MSVC-compatible object files and linker invocation.
/// On Windows targets, prefers MinGW `gcc` when running on Windows,
/// otherwise defaults to `cl.exe` (MSVC).
/// On Unix targets, defaults to `cc`.
pub fn detect_c_compiler_for_target(target: &Target) -> String {
    if let Ok(cc) = std::env::var("CC") {
        return cc;
    }
    // When SIMPLE_LINKER_FLAVOR=msvc, prefer MSVC-compatible compilers
    if is_msvc_linker_flavor() {
        for cc in &["clang-cl", "clang", "cl.exe"] {
            if command_exists(cc) && is_msvc_target(cc) {
                return cc.to_string();
            }
        }
    }
    match target.os {
        TargetOS::Windows => {
            if cfg!(target_os = "windows") && command_exists("gcc") {
                "gcc".to_string()
            } else if cfg!(target_os = "windows") && command_exists("cc") {
                "cc".to_string()
            } else {
                "cl.exe".to_string()
            }
        }
        _ => "cc".to_string(),
    }
}

/// Find a C++ compiler.
///
/// When `SIMPLE_LINKER_FLAVOR=msvc`, prefers `clang-cl` (handles C++ linking).
/// On Windows, tries clang++ then g++.
/// On Unix, tries clang++ then g++.
pub fn find_cxx_compiler() -> String {
    if let Ok(cxx) = std::env::var("CXX") {
        return cxx;
    }
    // When SIMPLE_LINKER_FLAVOR=msvc, prefer MSVC-compatible C++ compilers.
    // Try clang-cl first, then clang++ (may target MSVC), then plain clang
    // (handles .cpp files and targets MSVC on Windows standalone installs).
    if is_msvc_linker_flavor() {
        for cxx in &["clang-cl", "clang++", "clang"] {
            if command_exists(cxx) && is_msvc_target(cxx) {
                return cxx.to_string();
            }
        }
    }
    for cxx in &["clang++", "g++"] {
        if command_exists(cxx) {
            return cxx.to_string();
        }
    }
    "g++".to_string()
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
    std::env::var("SIMPLE_LINKER_FLAVOR").map_or(false, |v| v.eq_ignore_ascii_case("msvc"))
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
