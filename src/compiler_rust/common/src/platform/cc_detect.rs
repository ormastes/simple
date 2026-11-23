//! C/C++ compiler detection.
//!
//! Consolidated logic for finding available C and C++ compilers,
//! previously duplicated in `native_project.rs` and `native_binary.rs`.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use crate::platform::path::to_native_owned;
use crate::target::{LinkerFlavor, Target, TargetOS};

// Toolchain policy (2026-09-24): clang only -- never gcc/g++/cl.exe as a
// host compiler. A missing clang is reported by `require_compiler` with the
// install hint instead of silently switching to another toolchain.
const WINDOWS_GNU_C_COMPILERS: &[&str] = &["clang"];
const WINDOWS_GNU_CXX_COMPILERS: &[&str] = &["clang++"];
// Windows GNU drivers: prefer llvm-mingw's arch-matching triple-prefixed clang
// wrappers (`<arch>-w64-mingw32-clang`), never `x86_64-w64-mingw32-gcc`/`g++`
// and never an MSVC-target `clang`. The driver prefix follows the target arch
// (`i686-`/`aarch64-`/`armv7-`), so a 32-bit target is never compiled by the
// x86_64 wrapper.
fn windows_gnu_cross_driver(target: &Target, cxx: bool) -> String {
    use crate::target::TargetArch;
    let arch = match target.arch {
        TargetArch::X86 => "i686",
        TargetArch::Aarch64 => "aarch64",
        TargetArch::Arm => "armv7",
        // Riscv/Wasm never reach the Windows-GNU cross path.
        _ => "x86_64",
    };
    format!("{arch}-w64-mingw32-{}", if cxx { "clang++" } else { "clang" })
}
const MSVC_C_COMPILERS: &[&str] = &["clang-cl", "clang"];
const MSVC_CXX_COMPILERS: &[&str] = &["clang-cl", "clang++", "clang"];

/// Explicit environment inputs for deterministic compiler detection.
#[derive(Debug, Clone, Default)]
pub struct ToolDetectEnv {
    pub cc: Option<String>,
    pub cxx: Option<String>,
    pub path: Option<OsString>,
    pub llvm_mingw_root: Option<String>,
    pub simple_llvm_mingw_root: Option<String>,
    pub home_dir: Option<PathBuf>,
    pub userprofile_dir: Option<PathBuf>,
}

impl ToolDetectEnv {
    /// Capture compiler-detection inputs from the current process environment.
    pub fn from_process() -> Self {
        Self {
            cc: std::env::var("CC").ok(),
            cxx: std::env::var("CXX").ok(),
            path: std::env::var_os("PATH"),
            llvm_mingw_root: std::env::var("LLVM_MINGW_ROOT").ok(),
            simple_llvm_mingw_root: std::env::var("SIMPLE_LLVM_MINGW_ROOT").ok(),
            home_dir: std::env::var_os("HOME").filter(|v| !v.is_empty()).map(PathBuf::from),
            userprofile_dir: std::env::var_os("USERPROFILE").filter(|v| !v.is_empty()).map(PathBuf::from),
        }
    }
}

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
        _ => &["clang++"],
    }
}

/// Find a C compiler for the host platform.
///
/// Respects the `CC` environment variable. When `SIMPLE_LINKER_FLAVOR=msvc`,
/// prefers MSVC-compatible compilers (`clang-cl`). On Windows, prefers `clang-cl`.
/// On Unix, uses `clang` (clang-only toolchain).
pub fn find_c_compiler() -> String {
    detect_c_compiler_for_target(&Target::host())
}

fn nonblank_tool_override(value: String) -> Option<String> {
    (!value.trim().is_empty()).then(|| to_native_owned(value))
}

fn split_path_dirs(path_var: Option<&OsStr>) -> Vec<PathBuf> {
    path_var.map(std::env::split_paths).into_iter().flatten().collect()
}

fn push_unique_dir(dirs: &mut Vec<PathBuf>, dir: PathBuf) {
    if !dirs.contains(&dir) {
        dirs.push(dir);
    }
}

fn collect_llvm_mingw_bin_dirs_from_root(dirs: &mut Vec<PathBuf>, raw_root: Option<&str>) {
    let Some(raw) = raw_root.map(str::trim).filter(|s| !s.is_empty()) else {
        return;
    };
    let root = PathBuf::from(to_native_owned(raw.to_string()));
    let bin = root.join("bin");
    if bin.is_dir() {
        push_unique_dir(dirs, bin);
    }
    if root.is_dir() {
        push_unique_dir(dirs, root);
    }
}

fn llvm_mingw_toolchain_bin_dirs(env: &ToolDetectEnv) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    collect_llvm_mingw_bin_dirs_from_root(&mut dirs, env.llvm_mingw_root.as_deref());
    collect_llvm_mingw_bin_dirs_from_root(&mut dirs, env.simple_llvm_mingw_root.as_deref());

    let mut home_roots = Vec::new();
    if let Some(home) = env.home_dir.as_ref() {
        home_roots.push(home.clone());
    }
    if let Some(up) = env.userprofile_dir.as_ref() {
        if !home_roots.contains(up) {
            home_roots.push(up.clone());
        }
    }

    for home in home_roots {
        let toolchains_dir = home.join(".simple").join("toolchains");
        let Ok(entries) = std::fs::read_dir(&toolchains_dir) else {
            continue;
        };
        let mut matched: Vec<(String, PathBuf)> = entries
            .flatten()
            .filter_map(|entry| {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !name.to_ascii_lowercase().starts_with("llvm-mingw-") {
                    return None;
                }
                let bin = entry.path().join("bin");
                bin.is_dir().then_some((name, bin))
            })
            .collect();
        // Prefer newest dated llvm-mingw toolchain (e.g. llvm-mingw-20260922-ucrt-x86_64).
        matched.sort_by(|a, b| b.0.cmp(&a.0));
        for (_, bin) in matched {
            push_unique_dir(&mut dirs, bin);
        }
    }
    dirs
}

fn candidate_paths_in_dir(dir: &Path, name: &str) -> Vec<PathBuf> {
    #[cfg(target_os = "windows")]
    {
        let lower = name.to_ascii_lowercase();
        if lower.ends_with(".exe") || lower.ends_with(".cmd") || lower.ends_with(".bat") {
            vec![dir.join(name)]
        } else {
            vec![
                dir.join(format!("{name}.exe")),
                dir.join(format!("{name}.cmd")),
                dir.join(format!("{name}.bat")),
                dir.join(name),
            ]
        }
    }
    #[cfg(not(target_os = "windows"))]
    {
        vec![dir.join(name)]
    }
}

fn resolve_matching_command_in_dirs(
    name: &str,
    dirs: &[PathBuf],
    predicate: impl Fn(&str) -> bool,
) -> Option<String> {
    if name.contains(['/', '\\']) {
        return (command_works(name) && predicate(name)).then(|| name.to_string());
    }
    for dir in dirs {
        if !dir.is_dir() {
            continue;
        }
        for candidate in candidate_paths_in_dir(dir, name) {
            if candidate.is_file() {
                let candidate_str = candidate.to_string_lossy().into_owned();
                if command_works(&candidate_str) && predicate(&candidate_str) {
                    return Some(candidate_str);
                }
            }
        }
    }
    None
}

fn clang_effective_triple(cc: &str) -> Option<String> {
    for flag in ["--print-effective-triple", "-dumpmachine"] {
        if let Ok(output) = std::process::Command::new(cc).arg(flag).output() {
            if output.status.success() {
                let triple = String::from_utf8_lossy(&output.stdout).trim().to_ascii_lowercase();
                if !triple.is_empty() {
                    return Some(triple);
                }
            }
        }
    }
    None
}

fn is_windows_gnu_clang_driver(cc: &str) -> bool {
    clang_effective_triple(cc).is_some_and(|triple| {
        !triple.contains("windows-msvc")
            && (triple.contains("windows-gnu") || triple.contains("mingw") || triple.contains("windows-gnullvm"))
    })
}

fn detect_windows_gnu_compiler_with_env(target: &Target, cxx: bool, env: &ToolDetectEnv) -> String {
    let arch_driver = windows_gnu_cross_driver(target, cxx);
    let plain_drivers = if cxx {
        WINDOWS_GNU_CXX_COMPILERS
    } else {
        WINDOWS_GNU_C_COMPILERS
    };
    let path_dirs = split_path_dirs(env.path.as_deref());
    let toolchain_dirs = llvm_mingw_toolchain_bin_dirs(env);

    // 1. Prefer the arch-matching llvm-mingw driver on PATH.
    if let Some(resolved) = resolve_matching_command_in_dirs(&arch_driver, &path_dirs, |cc| !is_msvc_target(cc)) {
        return resolved;
    }
    // 2. Search explicit LLVM_MINGW_ROOT / SIMPLE_LLVM_MINGW_ROOT and
    //    $HOME/.simple/toolchains/llvm-mingw-*/bin for the arch-matching driver.
    if let Some(resolved) =
        resolve_matching_command_in_dirs(&arch_driver, &toolchain_dirs, |cc| !is_msvc_target(cc))
    {
        return resolved;
    }
    // 3. Fall back to plain clang/clang++ inside llvm-mingw toolchain roots,
    //    then PATH only when its effective target is Windows GNU (never MSVC,
    //    macOS, or Linux host clang).
    for plain in plain_drivers {
        if let Some(resolved) =
            resolve_matching_command_in_dirs(plain, &toolchain_dirs, |cc| !is_msvc_target(cc))
        {
            return resolved;
        }
    }
    for plain in plain_drivers {
        if let Some(resolved) = resolve_matching_command_in_dirs(plain, &path_dirs, |cc| {
            !is_msvc_target(cc) && is_windows_gnu_clang_driver(cc)
        }) {
            return resolved;
        }
    }
    // 4. Fail closed on the arch-matching llvm-mingw driver name rather than
    //    bare `clang` (which could accidentally invoke an MSVC clang on PATH).
    arch_driver
}

/// Detect the C compiler for a specific target platform.
///
/// The target's resolved linker flavor selects an ABI-compatible toolchain:
/// Windows GNU prefers `<arch>-w64-mingw32-clang` (never MSVC-target `clang`);
/// Windows MSVC prefers `clang-cl`. On Unix targets, uses `clang`.
pub fn detect_c_compiler_for_target(target: &Target) -> String {
    detect_c_compiler_for_target_with_env(target, &ToolDetectEnv::from_process())
}

/// Deterministic variant of [`detect_c_compiler_for_target`] using explicit `env`.
pub fn detect_c_compiler_for_target_with_env(target: &Target, env: &ToolDetectEnv) -> String {
    if let Some(cc) = env.cc.as_ref() {
        // MSYS does NOT path-convert env vars for native child processes, so a
        // `CC=/d/llvm/bin/clang-cl` arrives here verbatim and is unusable as a
        // program path. This value goes straight to `Command::new`, so it is a
        // spawn boundary and must be converted here. Identity on Unix.
        if let Some(selected) = nonblank_tool_override(cc.clone()) {
            return selected;
        }
    }
    let flavor = target.linker_flavor();
    if target.os == TargetOS::Windows && flavor == LinkerFlavor::Gnu {
        return detect_windows_gnu_compiler_with_env(target, false, env);
    }
    if flavor == LinkerFlavor::Msvc {
        let path_dirs = split_path_dirs(env.path.as_deref());
        for cc in MSVC_C_COMPILERS {
            if let Some(resolved) =
                resolve_matching_command_in_dirs(cc, &path_dirs, |c| compiler_matches_flavor(c, flavor))
            {
                return resolved;
            }
        }
        return "clang-cl".to_string();
    }
    "clang".to_string()
}

/// Error for a required clang compiler that is not installed (clang-only
/// toolchain; no gcc/g++/cl.exe fallback), naming the install command.
pub fn missing_compiler_error(tool: &str) -> String {
    format!(
        "required compiler `{tool}` was not found on PATH (clang-only toolchain;          gcc, g++ and MSVC cl.exe are not used as a fallback).          Install it with: sh scripts/setup/bootstrap-prereqs.shs install"
    )
}

/// Clang-only policy (CLAUDE.md Critical Rules: "Never use GCC"). The `CC`
/// override is honoured verbatim by `detect_c_compiler_for_target`, so a
/// `CC=gcc` or a bare `cc` that is really gcc-13 would otherwise reach
/// `Command::new` and link through collect2. Returns the refusal text, or
/// `None` when the driver is acceptable. Only the documented hosted cross
/// drivers (`DOCUMENTED_CROSS_GCC_DRIVERS`, the names `hosted_linux_cross_compiler`
/// and `windows_gnu_cross_driver` emits) are exempt — the QEMU cross lane's own,
/// still-open gap. Any other `*gcc*` basename, including a host-triple
/// `x86_64-linux-gnu-gcc-13`, is refused, matching the Simple side's
/// `c_driver_classify_v1`.
const DOCUMENTED_CROSS_GCC_DRIVERS: &[&str] = &[
    "aarch64-linux-gnu-gcc",
    "aarch64-linux-gnu-g++",
    "riscv64-linux-gnu-gcc",
    "riscv64-linux-gnu-g++",
    "arm-linux-gnueabihf-gcc",
    "arm-linux-gnueabihf-g++",
    "i686-linux-gnu-gcc",
    "i686-linux-gnu-g++",
    "x86_64-w64-mingw32-gcc",
    "x86_64-w64-mingw32-g++",
];

/// A documented cross gcc name is exempt only when it really cross-compiles:
/// on a Linux host, `<host-arch>-linux-gnu-gcc` is the host's own gcc.
fn cross_gcc_exempt(base: &str, host_arch: &str, host_os: &str) -> bool {
    if !DOCUMENTED_CROSS_GCC_DRIVERS.contains(&base) {
        return false;
    }
    let arch = base.split('-').next().unwrap_or("");
    !(host_os == "linux" && base.contains("-linux-gnu") && arch == host_arch)
}

pub fn gcc_driver_refusal(tool: &str, version_banner: &str) -> Option<String> {
    let base = tool.rsplit(['/', '\\']).next().unwrap_or(tool).to_ascii_lowercase();
    let base = base.strip_suffix(".exe").unwrap_or(&base);
    if cross_gcc_exempt(base, std::env::consts::ARCH, std::env::consts::OS) {
        return None;
    }
    let gcc_name = |stem: &str| {
        base == stem || base.starts_with(&format!("{stem}-")) || base.ends_with(&format!("-{stem}")) || base.contains(&format!("-{stem}-"))
    };
    let bare_gcc = gcc_name("gcc") || gcc_name("g++");
    let banner = version_banner.to_ascii_lowercase();
    let banner_is_gcc = !banner.contains("clang version")
        && (banner.contains("free software foundation") || banner.contains("gcc version") || banner.contains("(gcc)"));
    let generic_name = base == "cc" || base == "c++";
    if bare_gcc || (generic_name && banner_is_gcc) {
        return Some(format!(
            "clang-only policy (CLAUDE.md: Never use GCC): C driver `{tool}` is GCC. \
             gcc, g++ and a `cc` that resolves to gcc are never used as a fallback. \
             Fix: `. scripts/setup/llvm-toolchain-env.shs` (clang-23, ld.lld/mold on PATH) or set CC=clang"
        ));
    }
    None
}

fn version_banner(tool: &str) -> String {
    std::process::Command::new(tool)
        .arg("--version")
        .output()
        .map(|out| String::from_utf8_lossy(&out.stdout).lines().take(3).collect::<Vec<_>>().join("\n"))
        .unwrap_or_default()
}

/// Fail fast when the selected compiler cannot be run, or is GCC.
pub fn require_compiler(tool: &str) -> Result<(), String> {
    if let Some(refusal) = gcc_driver_refusal(tool, "") {
        return Err(refusal);
    }
    if !command_exists(tool) {
        return Err(missing_compiler_error(tool));
    }
    if let Some(refusal) = gcc_driver_refusal(tool, &version_banner(tool)) {
        return Err(refusal);
    }
    Ok(())
}

/// Find a C++ compiler.
///
/// Uses the host target's resolved linker flavor. Windows GNU uses `clang++`;
/// Windows MSVC prefers `clang-cl`. On Unix, `clang++`.
pub fn find_cxx_compiler() -> String {
    detect_cxx_compiler_for_target(&Target::host())
}

/// Detect the C++ compiler for a specific target platform.
///
/// An explicit `CXX` chooses the executable, while the target's resolved
/// linker flavor determines the ABI-compatible automatic candidates.
pub fn detect_cxx_compiler_for_target(target: &Target) -> String {
    detect_cxx_compiler_for_target_with_env(target, &ToolDetectEnv::from_process())
}

/// Deterministic variant of [`detect_cxx_compiler_for_target`] using explicit `env`.
pub fn detect_cxx_compiler_for_target_with_env(target: &Target, env: &ToolDetectEnv) -> String {
    if let Some(cxx) = env.cxx.as_ref() {
        // Same spawn-boundary reasoning as `CC` above. Identity on Unix.
        if let Some(selected) = nonblank_tool_override(cxx.clone()) {
            return selected;
        }
    }
    let flavor = target.linker_flavor();
    if target.os == TargetOS::Windows && flavor == LinkerFlavor::Gnu {
        return detect_windows_gnu_compiler_with_env(target, true, env);
    }
    let path_dirs = split_path_dirs(env.path.as_deref());
    for cxx in cxx_candidates(target, flavor) {
        if let Some(resolved) =
            resolve_matching_command_in_dirs(cxx, &path_dirs, |c| compiler_matches_flavor(c, flavor))
        {
            return resolved;
        }
    }
    if flavor == LinkerFlavor::Msvc {
        "clang-cl".to_string()
    } else {
        "clang++".to_string()
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
            "/opt/homebrew/opt/llvm/bin/llvm-ar",
            "/opt/homebrew/opt/llvm@18/bin/llvm-ar",
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
    let base = cc.rsplit(['/', '\\']).next().unwrap_or(cc);
    base.eq_ignore_ascii_case("cl") || base.eq_ignore_ascii_case("cl.exe")
}

/// Check if a C/C++ compiler targets the MSVC ABI.
///
/// Returns true for clang-cl, cl.exe, or any clang whose default target
/// triple contains "windows-msvc". This determines whether to use
/// MSVC-style linker flags (/WHOLEARCHIVE, /FORCE:UNRESOLVED) or
/// GNU-style (-Wl,--whole-archive, etc.).
pub fn is_msvc_target(cc: &str) -> bool {
    let base = cc.rsplit(['/', '\\']).next().unwrap_or(cc).to_ascii_lowercase();
    // clang-cl and cl.exe always target MSVC
    if base.contains("clang-cl") || is_msvc_compiler(cc) {
        return true;
    }
    // For clang/clang++ (including versioned or triple-prefixed clang drivers),
    // check the effective target triple.
    if base.contains("clang") {
        if let Some(triple) = clang_effective_triple(cc) {
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
fn command_works(name: &str) -> bool {
    std::process::Command::new(name)
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn windows_where_candidates(output: &[u8]) -> Vec<String> {
    String::from_utf8_lossy(output)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Resolve the first runnable installation of a command. Windows `where.exe`
/// can report several PATH hits; invoking only the bare name retries the first
/// broken installation forever and never reaches a later healthy compiler.
fn resolve_working_command(name: &str) -> Option<String> {
    #[cfg(target_os = "windows")]
    if !name.contains(['/', '\\']) {
        if let Ok(output) = std::process::Command::new("where.exe").arg(name).output() {
            if output.status.success() {
                for candidate in windows_where_candidates(&output.stdout) {
                    if command_works(&candidate) {
                        return Some(candidate);
                    }
                }
            }
        }
    }
    command_works(name).then(|| name.to_string())
}

pub fn command_exists(name: &str) -> bool {
    resolve_working_command(name).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::target::TargetArch;
    use std::sync::Mutex;

    static PROCESS_ENV_LOCK: Mutex<()> = Mutex::new(());

    struct EnvVarGuard {
        saved: Vec<(&'static str, Option<OsString>)>,
    }

    impl EnvVarGuard {
        fn capture(keys: &[&'static str]) -> Self {
            Self {
                saved: keys.iter().map(|&k| (k, std::env::var_os(k))).collect(),
            }
        }
    }

    impl Drop for EnvVarGuard {
        fn drop(&mut self) {
            for (k, v) in self.saved.drain(..) {
                match v {
                    Some(val) => std::env::set_var(k, val),
                    None => std::env::remove_var(k),
                }
            }
        }
    }

    fn write_stub_clang(dir: &Path, name: &str, effective_triple: &str) -> PathBuf {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let path = dir.join(name);
            let script = format!(
                "#!/bin/sh\nif [ \"$1\" = \"--print-effective-triple\" ] || [ \"$1\" = \"-dumpmachine\" ]; then\n  echo \"{effective_triple}\"\nfi\nexit 0\n"
            );
            std::fs::write(&path, script).unwrap();
            let mut perms = std::fs::metadata(&path).unwrap().permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(&path, perms).unwrap();
            path
        }
        #[cfg(windows)]
        {
            let path = dir.join(format!("{name}.cmd"));
            let script = format!(
                "@echo off\r\nif \"%1\"==\"--print-effective-triple\" echo {effective_triple}\r\nif \"%1\"==\"-dumpmachine\" echo {effective_triple}\r\nexit /b 0\r\n"
            );
            std::fs::write(&path, script).unwrap();
            path
        }
    }

    fn stem(path: &str) -> String {
        let base = path.rsplit(['/', '\\']).next().unwrap_or("").to_ascii_lowercase();
        for ext in [".exe", ".cmd", ".bat"] {
            if let Some(stripped) = base.strip_suffix(ext) {
                return stripped.to_string();
            }
        }
        base
    }

    #[test]
    fn gcc_drivers_are_refused_and_clang_is_not() {
        let fsf = "cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0\nCopyright (C) 2023 Free Software Foundation, Inc.";
        assert!(gcc_driver_refusal("gcc", "").is_some());
        assert!(gcc_driver_refusal("/usr/bin/g++-13", "").is_some());
        assert!(gcc_driver_refusal("cc", fsf).is_some());
        assert!(gcc_driver_refusal("cc", "").is_none(), "an unprobed `cc` is only refused once its banner says GCC");
        assert!(gcc_driver_refusal("cc", "Apple clang version 16.0.0").is_none());
        assert!(gcc_driver_refusal("clang-23", "clang version 23.1.0").is_none());
        assert!(gcc_driver_refusal("clang-cl.exe", "").is_none());
        assert!(gcc_driver_refusal("arm-linux-gnueabihf-gcc", "").is_none(), "documented hosted cross drivers are the cross lane's own gap");
        assert!(gcc_driver_refusal("/usr/bin/x86_64-linux-gnu-gcc-13", "").is_some(), "a host-triple gcc is still gcc");
        assert!(gcc_driver_refusal("mips-linux-gnu-gcc", "").is_some(), "undocumented cross gcc is refused");
        let message = gcc_driver_refusal("gcc", "").unwrap();
        assert!(message.contains("Never use GCC") && message.contains("llvm-toolchain-env.shs"), "{message}");
    }

    #[test]
    fn blank_tool_overrides_use_target_detection() {
        assert!(nonblank_tool_override(String::new()).is_none());
        assert!(nonblank_tool_override(" \t ".to_string()).is_none());
        assert!(nonblank_tool_override("clang++".to_string()).is_some());
    }

    #[test]
    fn windows_gnu_cross_driver_follows_target_arch() {
        // cross_compile_linker_matrix_2026-11-17 (d): i686 used to get the
        // x86_64 llvm-mingw driver and silently build 64-bit objects.
        let empty = ToolDetectEnv::default();
        for (triple, cc, cxx) in [
            ("x86_64-pc-windows-gnu", "x86_64-w64-mingw32-clang", "x86_64-w64-mingw32-clang++"),
            ("i686-pc-windows-gnu", "i686-w64-mingw32-clang", "i686-w64-mingw32-clang++"),
            ("aarch64-pc-windows-gnu", "aarch64-w64-mingw32-clang", "aarch64-w64-mingw32-clang++"),
            ("armv7-pc-windows-gnu", "armv7-w64-mingw32-clang", "armv7-w64-mingw32-clang++"),
        ] {
            let target = Target::parse(triple).unwrap();
            assert_eq!(windows_gnu_cross_driver(&target, false), cc, "{triple}");
            assert_eq!(windows_gnu_cross_driver(&target, true), cxx, "{triple}");
            assert_eq!(detect_c_compiler_for_target_with_env(&target, &empty), cc, "{triple}");
            assert_eq!(detect_cxx_compiler_for_target_with_env(&target, &empty), cxx, "{triple}");
            assert!(gcc_driver_refusal(&windows_gnu_cross_driver(&target, false), "").is_none());
        }
    }

    #[test]
    fn windows_gnu_uses_clang_candidates() {
        let target = Target::parse("x86_64-pc-windows-gnu").unwrap();
        assert_eq!(WINDOWS_GNU_C_COMPILERS, &["clang"]);
        assert_eq!(cxx_candidates(&target, LinkerFlavor::Gnu), &["clang++"]);
        assert!(!compiler_matches_flavor("clang-cl", LinkerFlavor::Gnu));
        assert_eq!(target.linker_flavor(), LinkerFlavor::Gnu);
        assert_eq!(target.triple_str(), "x86_64-pc-windows-gnu");

        let empty = ToolDetectEnv::default();
        assert_eq!(detect_c_compiler_for_target_with_env(&target, &empty), "x86_64-w64-mingw32-clang");
        assert_eq!(detect_cxx_compiler_for_target_with_env(&target, &empty), "x86_64-w64-mingw32-clang++");
        for cxx_driver in [false, true] {
            let driver = windows_gnu_cross_driver(&target, cxx_driver);
            assert!(gcc_driver_refusal(&driver, "").is_none(), "{driver}");
        }
    }

    #[test]
    fn windows_gnu_prefers_arch_llvm_mingw_and_rejects_msvc_clang_ahead_on_path() {
        let temp = tempfile::tempdir().unwrap();
        let msvc_bin = temp.path().join("llvm-msvc").join("bin");
        let host_bin = temp.path().join("host").join("bin");
        let mingw_bin = temp.path().join("llvm-mingw").join("bin");
        let mingw_plain_bin = temp.path().join("mingw-plain").join("bin");
        std::fs::create_dir_all(&msvc_bin).unwrap();
        std::fs::create_dir_all(&host_bin).unwrap();
        std::fs::create_dir_all(&mingw_bin).unwrap();
        std::fs::create_dir_all(&mingw_plain_bin).unwrap();

        let msvc_clang = write_stub_clang(&msvc_bin, "clang", "x86_64-pc-windows-msvc");
        let msvc_clangxx = write_stub_clang(&msvc_bin, "clang++", "x86_64-pc-windows-msvc");
        assert!(is_msvc_target(msvc_clang.to_str().unwrap()));
        assert!(is_msvc_target(msvc_clangxx.to_str().unwrap()));

        // Host non-Windows clang (e.g., Apple or Linux clang) must not satisfy Windows GNU on PATH.
        let _host_clang = write_stub_clang(&host_bin, "clang", "arm64-apple-darwin25.5.0");
        let _host_clangxx = write_stub_clang(&host_bin, "clang++", "arm64-apple-darwin25.5.0");

        let i686_cc = write_stub_clang(&mingw_bin, "i686-w64-mingw32-clang", "i686-w64-windows-gnu");
        let i686_cxx = write_stub_clang(&mingw_bin, "i686-w64-mingw32-clang++", "i686-w64-windows-gnu");
        let x86_64_cc = write_stub_clang(&mingw_bin, "x86_64-w64-mingw32-clang", "x86_64-w64-windows-gnu");
        let x86_64_cxx = write_stub_clang(&mingw_bin, "x86_64-w64-mingw32-clang++", "x86_64-w64-windows-gnu");
        let aarch64_cc = write_stub_clang(&mingw_bin, "aarch64-w64-mingw32-clang", "aarch64-w64-windows-gnu");
        let aarch64_cxx = write_stub_clang(&mingw_bin, "aarch64-w64-mingw32-clang++", "aarch64-w64-windows-gnu");
        let _mingw_clang = write_stub_clang(&mingw_bin, "clang", "x86_64-w64-windows-gnu");
        assert!(!is_msvc_target(i686_cc.to_str().unwrap()));

        let path_with_msvc_first = std::env::join_paths([&msvc_bin, &host_bin, &mingw_bin]).unwrap();
        let env = ToolDetectEnv {
            path: Some(path_with_msvc_first),
            ..ToolDetectEnv::default()
        };

        for (triple, expected_cc, expected_cxx) in [
            ("i686-pc-windows-gnu", &i686_cc, &i686_cxx),
            ("x86_64-pc-windows-gnu", &x86_64_cc, &x86_64_cxx),
            ("aarch64-pc-windows-gnu", &aarch64_cc, &aarch64_cxx),
        ] {
            let target = Target::parse(triple).unwrap();
            let got_cc = detect_c_compiler_for_target_with_env(&target, &env);
            let got_cxx = detect_cxx_compiler_for_target_with_env(&target, &env);
            assert_eq!(Path::new(&got_cc), expected_cc.as_path(), "{triple}");
            assert_eq!(Path::new(&got_cxx), expected_cxx.as_path(), "{triple}");
            assert_ne!(Path::new(&got_cc), msvc_clang.as_path(), "{triple}");
            assert!(!is_msvc_target(&got_cc), "{triple}");
        }

        // Only MSVC clang and non-Windows host clang on PATH: never fall back to either!
        let msvc_and_host_only = ToolDetectEnv {
            path: Some(std::env::join_paths([&msvc_bin, &host_bin]).unwrap()),
            ..ToolDetectEnv::default()
        };
        let i686 = Target::parse("i686-pc-windows-gnu").unwrap();
        assert_eq!(detect_c_compiler_for_target_with_env(&i686, &msvc_and_host_only), "i686-w64-mingw32-clang");
        assert_eq!(detect_cxx_compiler_for_target_with_env(&i686, &msvc_and_host_only), "i686-w64-mingw32-clang++");

        // Plain GNU clang (windows-gnu triple) on PATH after MSVC clang is accepted ONLY when
        // no <arch>-w64-mingw32-clang exists anywhere.
        let mingw_plain_clang = write_stub_clang(&mingw_plain_bin, "clang", "x86_64-w64-windows-gnu");
        let plain_fallback_env = ToolDetectEnv {
            path: Some(std::env::join_paths([&msvc_bin, &host_bin, &mingw_plain_bin]).unwrap()),
            ..ToolDetectEnv::default()
        };
        let got_plain = detect_c_compiler_for_target_with_env(&i686, &plain_fallback_env);
        assert_eq!(Path::new(&got_plain), mingw_plain_clang.as_path());
        assert_ne!(Path::new(&got_plain), msvc_clang.as_path());
    }

    #[test]
    fn windows_gnu_discovers_toolchain_roots_and_home_llvm_mingw() {
        let temp = tempfile::tempdir().unwrap();
        let msvc_bin = temp.path().join("llvm-msvc").join("bin");
        let root_dir = temp.path().join("custom-mingw");
        let root_bin = root_dir.join("bin");
        let home_dir = temp.path().join("home");
        let old_home_bin = home_dir
            .join(".simple")
            .join("toolchains")
            .join("llvm-mingw-20250101-ucrt-x86_64")
            .join("bin");
        let new_home_bin = home_dir
            .join(".simple")
            .join("toolchains")
            .join("llvm-mingw-20260922-ucrt-x86_64")
            .join("bin");
        for dir in [&msvc_bin, &root_bin, &old_home_bin, &new_home_bin] {
            std::fs::create_dir_all(dir).unwrap();
        }

        let _msvc_clang = write_stub_clang(&msvc_bin, "clang", "x86_64-pc-windows-msvc");
        let root_i686 = write_stub_clang(&root_bin, "i686-w64-mingw32-clang", "i686-w64-windows-gnu");
        let _old_i686 = write_stub_clang(&old_home_bin, "i686-w64-mingw32-clang", "i686-w64-windows-gnu");
        let new_i686 = write_stub_clang(&new_home_bin, "i686-w64-mingw32-clang", "i686-w64-windows-gnu");
        let new_x86_64 = write_stub_clang(&new_home_bin, "x86_64-w64-mingw32-clang", "x86_64-w64-windows-gnu");
        let new_aarch64 = write_stub_clang(&new_home_bin, "aarch64-w64-mingw32-clang", "aarch64-w64-windows-gnu");

        let i686 = Target::parse("i686-pc-windows-gnu").unwrap();
        let x86_64 = Target::parse("x86_64-pc-windows-gnu").unwrap();
        let aarch64 = Target::parse("aarch64-pc-windows-gnu").unwrap();

        // LLVM_MINGW_ROOT wins ahead of $HOME/.simple/toolchains when not on PATH.
        let root_env = ToolDetectEnv {
            path: Some(msvc_bin.as_os_str().to_os_string()),
            llvm_mingw_root: Some(root_dir.to_string_lossy().into_owned()),
            home_dir: Some(home_dir.clone()),
            ..ToolDetectEnv::default()
        };
        assert_eq!(Path::new(&detect_c_compiler_for_target_with_env(&i686, &root_env)), root_i686.as_path());

        // Without LLVM_MINGW_ROOT, newest $HOME/.simple/toolchains/llvm-mingw-*/bin is chosen.
        let home_env = ToolDetectEnv {
            path: Some(msvc_bin.as_os_str().to_os_string()),
            home_dir: Some(home_dir),
            ..ToolDetectEnv::default()
        };
        assert_eq!(Path::new(&detect_c_compiler_for_target_with_env(&i686, &home_env)), new_i686.as_path());
        assert_eq!(Path::new(&detect_c_compiler_for_target_with_env(&x86_64, &home_env)), new_x86_64.as_path());
        assert_eq!(Path::new(&detect_c_compiler_for_target_with_env(&aarch64, &home_env)), new_aarch64.as_path());
    }

    #[test]
    fn windows_gnu_process_env_rejects_msvc_clang_ahead_of_i686_mingw() {
        let _lock = PROCESS_ENV_LOCK.lock().unwrap();
        let _guard = EnvVarGuard::capture(&[
            "CC",
            "CXX",
            "PATH",
            "HOME",
            "USERPROFILE",
            "LLVM_MINGW_ROOT",
            "SIMPLE_LLVM_MINGW_ROOT",
            "SIMPLE_WINDOWS_ABI",
            "SIMPLE_LINKER_FLAVOR",
        ]);

        let temp = tempfile::tempdir().unwrap();
        let msvc_bin = temp.path().join("msvc").join("bin");
        let mingw_bin = temp.path().join("mingw").join("bin");
        std::fs::create_dir_all(&msvc_bin).unwrap();
        std::fs::create_dir_all(&mingw_bin).unwrap();
        let _msvc_clang = write_stub_clang(&msvc_bin, "clang", "x86_64-pc-windows-msvc");
        let i686_mingw = write_stub_clang(&mingw_bin, "i686-w64-mingw32-clang", "i686-w64-windows-gnu");
        let x86_64_mingw = write_stub_clang(&mingw_bin, "x86_64-w64-mingw32-clang", "x86_64-w64-windows-gnu");
        let aarch64_mingw = write_stub_clang(&mingw_bin, "aarch64-w64-mingw32-clang", "aarch64-w64-windows-gnu");

        std::env::remove_var("CC");
        std::env::remove_var("CXX");
        std::env::remove_var("LLVM_MINGW_ROOT");
        std::env::remove_var("SIMPLE_LLVM_MINGW_ROOT");
        std::env::set_var("HOME", temp.path());
        std::env::set_var("USERPROFILE", temp.path());
        std::env::set_var("SIMPLE_WINDOWS_ABI", "gnu");
        std::env::set_var("SIMPLE_LINKER_FLAVOR", "gnu");
        std::env::set_var("PATH", std::env::join_paths([&msvc_bin, &mingw_bin]).unwrap());

        assert_eq!(
            stem(&detect_c_compiler_for_target(&Target::parse("i686-pc-windows-gnu").unwrap())),
            "i686-w64-mingw32-clang"
        );
        assert_eq!(
            Path::new(&detect_c_compiler_for_target(&Target::parse("i686-pc-windows-gnu").unwrap())),
            i686_mingw.as_path()
        );
        assert_eq!(
            Path::new(&detect_c_compiler_for_target(&Target::parse("x86_64-pc-windows-gnu").unwrap())),
            x86_64_mingw.as_path()
        );
        assert_eq!(
            Path::new(&detect_c_compiler_for_target(&Target::parse("aarch64-pc-windows-gnu").unwrap())),
            aarch64_mingw.as_path()
        );

        // Explicit CC override still takes precedence.
        std::env::set_var("CC", "/custom/explicit-cc");
        assert_eq!(
            detect_c_compiler_for_target(&Target::parse("i686-pc-windows-gnu").unwrap()),
            "/custom/explicit-cc"
        );
    }

    #[test]
    fn windows_msvc_keeps_msvc_compilers() {
        let target = Target::parse("x86_64-pc-windows-msvc").unwrap();
        assert_eq!(MSVC_C_COMPILERS, &["clang-cl", "clang"]);
        assert_eq!(
            cxx_candidates(&target, LinkerFlavor::Msvc),
            &["clang-cl", "clang++", "clang"]
        );
        assert!(compiler_matches_flavor("clang-cl", LinkerFlavor::Msvc));
        assert_eq!(target.linker_flavor(), LinkerFlavor::Msvc);
        assert_eq!(target.triple_str(), "x86_64-pc-windows-msvc");
        if cfg!(target_os = "windows") {
            let resolved = detect_cxx_compiler_for_target(&target);
            assert!(
                command_works(&resolved),
                "resolved compiler is not runnable: {resolved}"
            );
            assert!(
                is_msvc_target(&resolved),
                "resolved compiler has the wrong ABI: {resolved}"
            );
        }
    }

    #[test]
    fn windows_where_candidates_preserve_all_installations_in_order() {
        assert_eq!(
            windows_where_candidates(b"C:\\broken\\clang-cl.exe\r\nC:\\healthy\\clang-cl.exe\r\n"),
            vec![
                "C:\\broken\\clang-cl.exe".to_string(),
                "C:\\healthy\\clang-cl.exe".to_string(),
            ]
        );
    }

    #[test]
    fn host_compiler_candidates_are_clang_only() {
        for list in [WINDOWS_GNU_C_COMPILERS, WINDOWS_GNU_CXX_COMPILERS, MSVC_C_COMPILERS, MSVC_CXX_COMPILERS] {
            for cc in list {
                assert!(!matches!(*cc, "gcc" | "g++" | "cc" | "c++" | "cl" | "cl.exe"), "{cc}");
            }
        }
        let linux = Target::new(TargetArch::X86_64, TargetOS::Linux);
        assert_eq!(cxx_candidates(&linux, LinkerFlavor::Gnu), &["clang++"]);
    }

    #[test]
    fn missing_compiler_error_names_tool_and_install_command() {
        let message = missing_compiler_error("clang-cl");
        assert!(message.contains("`clang-cl`"), "{message}");
        assert!(message.contains("sh scripts/setup/bootstrap-prereqs.shs install"), "{message}");
        assert!(require_compiler("definitely-not-a-compiler-xyz").is_err());
    }

    #[test]
    fn cross_gcc_exemption_requires_a_foreign_arch() {
        assert!(!cross_gcc_exempt("aarch64-linux-gnu-gcc", "aarch64", "linux"));
        assert!(cross_gcc_exempt("aarch64-linux-gnu-gcc", "x86_64", "linux"));
        assert!(cross_gcc_exempt("riscv64-linux-gnu-gcc", "aarch64", "linux"));
        assert!(cross_gcc_exempt("x86_64-w64-mingw32-gcc", "aarch64", "linux"));
        assert!(!cross_gcc_exempt("gcc", "aarch64", "linux"));
    }
}
