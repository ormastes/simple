//! Tool detection (C compiler, archive tool, linker detection),
//! runtime library discovery, system symbol identification,
//! and LLVM constructor stripping.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::path::{Path, PathBuf};

use super::{effective_target, safe_canonicalize, RUNTIME_PATH_OVERRIDE};
use simple_common::CORE_REQUIRED_RUNTIME_SYMBOLS;

fn has_nonempty_archive_payload(path: &Path) -> bool {
    path.is_file() && path.metadata().map(|meta| meta.len() > 0).unwrap_or(false)
}

fn archive_is_fresh_for_runtime_inputs(archive: &Path, runtime_root: &Path, inputs: &[&str]) -> bool {
    let archive_modified = match archive.metadata().and_then(|meta| meta.modified()) {
        Ok(modified) => modified,
        Err(_) => return false,
    };

    inputs.iter().all(|input| {
        let input_modified = runtime_root.join(input).metadata().and_then(|meta| meta.modified());
        matches!(input_modified, Ok(modified) if modified <= archive_modified)
    })
}

pub(crate) fn runtime_inputs_fingerprint(runtime_root: &Path, inputs: &[&str]) -> Option<String> {
    // Stable FNV-1a is sufficient for cache invalidation and avoids a hashing dependency.
    let mut hash = 0xcbf29ce484222325_u64;
    for input in inputs {
        for byte in input.as_bytes().iter().chain([0].iter()) {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        for byte in std::fs::read(runtime_root.join(input)).ok()? {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    Some(format!("{hash:016x}"))
}

fn archive_has_exact_runtime_members(archive: &Path, inputs: &[&str]) -> bool {
    let tool = find_archive_tool();
    let output = archive_list_command(&tool, archive).output();
    let Ok(output) = output else {
        return false;
    };
    if !output.status.success() {
        return false;
    }
    let mut actual: Vec<String> = String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect();
    let mut expected: Vec<String> = inputs
        .iter()
        .copied()
        .filter(|input| input.ends_with(".c"))
        .map(|input| format!("{}.{}", input.trim_end_matches(".c"), host_object_extension()))
        .collect();
    actual.sort();
    expected.sort();
    actual == expected
}

fn archive_from_dir(dir: &Path, stem: &str) -> Option<PathBuf> {
    let deps_lib = dir.join("deps").join(format!("{stem}.a"));
    if has_nonempty_archive_payload(&deps_lib) {
        return Some(deps_lib);
    }
    let lib = dir.join(format!("{stem}.a"));
    if has_nonempty_archive_payload(&lib) {
        return Some(lib);
    }
    #[cfg(target_os = "windows")]
    {
        let win_lib = match stem {
            "libsimple_runtime" => "simple_runtime.lib",
            "libsimple_native_all" => "simple_native_all.lib",
            _ => "",
        };
        if !win_lib.is_empty() {
            let path = dir.join(win_lib);
            if has_nonempty_archive_payload(&path) {
                return Some(path);
            }
        }
    }
    None
}

fn archive_from_path_or_dir(path: &Path, stem: &str) -> Option<PathBuf> {
    if path.is_dir() {
        return archive_from_dir(path, stem);
    }
    if has_nonempty_archive_payload(path) {
        return Some(path.to_path_buf());
    }
    None
}

/// Find a C compiler -- delegates to `simple_common::platform::cc_detect`.
pub(crate) fn find_c_compiler() -> String {
    simple_common::platform::cc_detect::find_c_compiler()
}

/// Find an archive tool -- delegates to `simple_common::platform::cc_detect`.
pub(crate) fn find_archive_tool() -> String {
    simple_common::platform::cc_detect::find_archive_tool()
}

fn is_msvc_archive_tool(tool: &str) -> bool {
    Path::new(tool)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .is_some_and(|stem| stem.eq_ignore_ascii_case("lib"))
}

pub(super) fn archive_create_command(
    tool: &str,
    archive: &Path,
    objects: &[PathBuf],
    append: bool,
    deterministic: bool,
) -> std::process::Command {
    let mut command = std::process::Command::new(tool);
    if is_msvc_archive_tool(tool) {
        command.arg("/NOLOGO").arg(format!("/OUT:{}", archive.display()));
        if append {
            command.arg(archive);
        }
    } else {
        let mode = match (append, deterministic) {
            (false, false) => "rcs",
            (true, false) => "rs",
            (false, true) => "rcsD",
            (true, true) => "rsD",
        };
        command.arg(mode).arg(archive);
    }
    command.args(objects);
    command
}

pub(super) fn archive_list_command(tool: &str, archive: &Path) -> std::process::Command {
    let mut command = std::process::Command::new(tool);
    if is_msvc_archive_tool(tool) {
        command.arg("/NOLOGO").arg("/LIST").arg(archive);
    } else {
        command.arg("t").arg(archive);
    }
    command
}

pub(crate) fn find_cxx_compiler() -> String {
    simple_common::platform::cc_detect::find_cxx_compiler()
}

pub(crate) fn hosted_linux_cross_compiler(
    target: simple_common::target::Target,
    needs_cxx: bool,
) -> Option<&'static str> {
    if target.os != simple_common::target::TargetOS::Linux || target.is_host() {
        return None;
    }
    match (target.arch, needs_cxx) {
        (simple_common::target::TargetArch::Aarch64, false) => Some("aarch64-linux-gnu-gcc"),
        (simple_common::target::TargetArch::Aarch64, true) => Some("aarch64-linux-gnu-g++"),
        (simple_common::target::TargetArch::Riscv64, false) => Some("riscv64-linux-gnu-gcc"),
        (simple_common::target::TargetArch::Riscv64, true) => Some("riscv64-linux-gnu-g++"),
        (simple_common::target::TargetArch::Arm, false) => Some("arm-linux-gnueabihf-gcc"),
        (simple_common::target::TargetArch::Arm, true) => Some("arm-linux-gnueabihf-g++"),
        (simple_common::target::TargetArch::X86, false) => Some("i686-linux-gnu-gcc"),
        (simple_common::target::TargetArch::X86, true) => Some("i686-linux-gnu-g++"),
        _ => None,
    }
}

pub(crate) fn target_c_compiler(target: simple_common::target::Target) -> String {
    hosted_linux_cross_compiler(target, false)
        .map(str::to_string)
        .unwrap_or_else(find_c_compiler)
}

pub(crate) fn target_cxx_compiler(target: simple_common::target::Target) -> String {
    hosted_linux_cross_compiler(target, true)
        .map(str::to_string)
        .unwrap_or_else(find_cxx_compiler)
}

/// Return the linker arguments for terminfo symbols used by hosted LLVM.
pub(crate) fn terminfo_link_args(target: simple_common::target::Target) -> Vec<String> {
    if target.os != simple_common::target::TargetOS::Linux {
        return Vec::new();
    }

    if target.is_host() {
        if let Ok(output) = std::process::Command::new("pkg-config")
            .args(["--libs", "tinfo"])
            .output()
        {
            if output.status.success() {
                let args = String::from_utf8_lossy(&output.stdout)
                    .split_whitespace()
                    .map(ToOwned::to_owned)
                    .collect::<Vec<_>>();
                if !args.is_empty() {
                    return args;
                }
            }
        }
    }

    vec!["-ltinfo".to_string()]
}

fn host_archive_name() -> &'static str {
    #[cfg(target_os = "windows")]
    {
        "simple_runtime.lib"
    }
    #[cfg(not(target_os = "windows"))]
    {
        "libsimple_runtime.a"
    }
}

fn host_object_extension() -> &'static str {
    #[cfg(target_os = "windows")]
    {
        "obj"
    }
    #[cfg(not(target_os = "windows"))]
    {
        "o"
    }
}

pub(crate) fn core_c_target_flags(
    target: simple_common::target::Target,
    source: &str,
    riscv_vector: bool,
) -> Vec<&'static str> {
    let mut flags = Vec::new();
    if target.arch == simple_common::target::TargetArch::Aarch64 {
        flags.push("-mno-outline-atomics");
    }
    if source == "runtime_simd_dispatch.c" && target.arch == simple_common::target::TargetArch::Riscv64 && riscv_vector
    {
        flags.extend(["-march=rv64gcv", "-mabi=lp64d"]);
    }
    flags
}

fn find_core_c_runtime_source_root() -> Option<PathBuf> {
    let mut candidates = Vec::new();

    if let Ok(cwd) = std::env::current_dir() {
        candidates.push(cwd);
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    candidates.push(manifest_dir);

    for base in candidates {
        for ancestor in base.ancestors() {
            let runtime_root = ancestor.join("src").join("runtime");
            if runtime_root.join("runtime.c").exists() && runtime_root.join("runtime_native.c").exists() {
                return Some(runtime_root);
            }
        }
    }

    None
}

fn build_c_runtime_library(build_dir: &Path, include_stage4_hosted: bool) -> Option<PathBuf> {
    let archive = build_dir.join(host_archive_name());
    let runtime_root = find_core_c_runtime_source_root()?;
    let target = effective_target();
    let mut runtime_inputs = vec![
        "runtime_native.c",
        "runtime_directx_core.c",
        "runtime_legacy_core.c",
        "runtime_mcp_core.c",
        "runtime_font.c",
        "runtime_pool.c",
        "runtime_simd_utf8.c",
        // engine2d SIMD row kernels (C/NEON) backing rt_engine2d_simd_*_row_u32;
        // replaces the Rust-seed engine2d_simd_ops backing for native builds.
        "runtime_simd_dispatch.c",
        "runtime_value.h",
        "runtime.h",
        "runtime_fork.h",
        "runtime_memtrack.h",
        "runtime_simd_dispatch.h",
        "runtime_thread.h",
        "platform/platform.h",
    ];
    if target.os == simple_common::target::TargetOS::Linux {
        // The portable compositor remains in the full CLI closure on Linux.
        // Reuse its canonical non-target providers so live Cocoa/Win32 calls
        // fail closed instead of becoming generated bootstrap stubs.
        runtime_inputs.extend(["hosted_cocoa.c", "hosted_win32.c"]);
    }
    if std::env::var("SIMPLE_CORE_C_INCLUDE_HTTPS_OPENSSL").ok().as_deref() == Some("1") {
        runtime_inputs.push("runtime_https_openssl_core.c");
    }
    if include_stage4_hosted {
        runtime_inputs.extend(["runtime_font.c", "runtime_memtrack.c", "runtime_sqlite.c"]);
    }

    let fingerprint = runtime_inputs_fingerprint(&runtime_root, &runtime_inputs)?;
    let fingerprint_path = build_dir.join(format!("{}.inputs.fingerprint", host_archive_name()));

    if has_nonempty_archive_payload(&archive)
        && archive_is_fresh_for_runtime_inputs(&archive, &runtime_root, &runtime_inputs)
        && archive_has_exact_runtime_members(&archive, &runtime_inputs)
        && std::fs::read_to_string(&fingerprint_path).ok().as_deref() == Some(fingerprint.as_str())
    {
        return Some(archive);
    }

    std::fs::create_dir_all(build_dir).ok()?;

    let cc = target_c_compiler(target);
    let ar = find_archive_tool();
    let obj_ext = host_object_extension();
    let mut objects = Vec::new();

    for source in runtime_inputs.iter().copied().filter(|input| input.ends_with(".c")) {
        let object = build_dir.join(format!("{}.{}", source.trim_end_matches(".c"), obj_ext));
        let riscv_vector = std::env::var("SIMPLE_RUNTIME_RISCV64_VECTOR").ok().as_deref() == Some("1");
        let status = std::process::Command::new(&cc)
            .arg("-c")
            .arg("-Os")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-fno-unwind-tables")
            .arg("-fno-asynchronous-unwind-tables")
            .arg("-fno-stack-protector")
            .arg("-fPIC")
            .arg("-std=gnu11")
            .args(core_c_target_flags(target, source, riscv_vector))
            .arg(format!("-I{}", runtime_root.display()))
            .arg(format!("-I{}", runtime_root.join("platform").display()))
            .arg(runtime_root.join(source))
            .arg("-o")
            .arg(&object)
            .status()
            .ok()?;
        if !status.success() {
            return None;
        }
        objects.push(object);
    }

    let status = archive_create_command(&ar, &archive, &objects, false, false)
        .status()
        .ok()?;
    if status.success() && has_nonempty_archive_payload(&archive) {
        std::fs::write(fingerprint_path, fingerprint).ok()?;
        Some(archive)
    } else {
        None
    }
}

pub(crate) fn build_core_c_runtime_library(build_dir: &Path) -> Option<PathBuf> {
    build_c_runtime_library(build_dir, false)
}

pub(crate) fn build_stage4_c_runtime_library(build_dir: &Path) -> Option<PathBuf> {
    build_c_runtime_library(build_dir, true)
}

/// Find the pure-Simple core runtime library.
pub(crate) fn find_simple_core_runtime_library() -> Option<PathBuf> {
    if let Some(dir) = RUNTIME_PATH_OVERRIDE.get() {
        for lane_dir in ["simple-core", "simple_core"] {
            if let Some(path) = archive_from_dir(&dir.join(lane_dir), "libsimple_runtime") {
                return Some(path);
            }
        }
    }

    for env_var in ["SIMPLE_SIMPLE_CORE_PATH", "SIMPLE_CORE_RUNTIME_PATH"] {
        if let Ok(path) = std::env::var(env_var) {
            let p = PathBuf::from(path);
            if let Some(found) = archive_from_path_or_dir(&p, "libsimple_runtime") {
                return Some(found);
            }
        }
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            for lane_dir in ["simple-core", "simple_core"] {
                if let Some(path) = archive_from_dir(&dir.join(lane_dir), "libsimple_runtime") {
                    return Some(path);
                }
            }
        }
    }

    let candidates = [
        "build/simple-core/deps/libsimple_runtime.a",
        "build/simple-core/libsimple_runtime.a",
        "build/simple_core/deps/libsimple_runtime.a",
        "build/simple_core/libsimple_runtime.a",
    ];

    for candidate in candidates {
        let path = PathBuf::from(candidate);
        if has_nonempty_archive_payload(&path) {
            return Some(path);
        }
    }

    None
}

/// Resolve the `nm`-style symbol-table reader to use for scanning archives and
/// object files.
///
/// Rationale: `std::process::Command::new("nm")` on macOS resolves to Xcode's
/// bundled `nm`, whose LLVM reader generation can lag behind the LLVM IR
/// generation rustc emits into `.rlib`/`.a` members. When that happens, `nm`
/// silently drops the unreadable archive members instead of erroring, so
/// defined-symbol scans under-report and legitimately-defined symbols get
/// misclassified as undefined (spurious stub generation). The same applies to
/// an *older* `llvm-nm` (e.g. the bootstrap script prepends the LLVM 18 keg to
/// `PATH` for the llvm-lib backend, and LLVM 18's reader rejects rustc 1.94's
/// LLVM 21-tagged members), so "any llvm-nm" is not sufficient — pick the
/// NEWEST reader available:
/// 1. `SIMPLE_NM` env override, if set (used verbatim).
/// 2. The highest-LLVM-version `llvm-nm` among: `llvm-nm` on `PATH` and the
///    Homebrew keg-only `llvm*` formulae (which don't symlink `llvm-nm` onto
///    `PATH`): `/opt/homebrew/opt/llvm*/bin/llvm-nm`,
///    `/usr/local/opt/llvm*/bin/llvm-nm`.
/// 3. Fall back to plain `nm`.
pub(super) fn nm_command() -> std::process::Command {
    static NM_TOOL: std::sync::OnceLock<PathBuf> = std::sync::OnceLock::new();
    let tool = NM_TOOL.get_or_init(|| {
        if let Ok(path) = std::env::var("SIMPLE_NM") {
            if !path.is_empty() {
                return PathBuf::from(path);
            }
        }

        let mut candidates: Vec<PathBuf> = Vec::new();
        if let Some(path) = which_on_path("llvm-nm") {
            candidates.push(path);
        }
        candidates.extend(homebrew_llvm_nm_candidates());

        let best = candidates
            .into_iter()
            .filter_map(|path| llvm_nm_major_version(&path).map(|version| (version, path)))
            .max_by_key(|(version, _)| *version);
        match best {
            Some((_, path)) => path,
            None => PathBuf::from("nm"),
        }
    });
    std::process::Command::new(tool)
}

fn which_on_path(tool: &str) -> Option<PathBuf> {
    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join(tool);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn homebrew_llvm_nm_candidates() -> Vec<PathBuf> {
    let mut found = Vec::new();
    for prefix in ["/opt/homebrew/opt", "/usr/local/opt"] {
        let Ok(entries) = std::fs::read_dir(prefix) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if !name.starts_with("llvm") {
                continue;
            }
            let candidate = entry.path().join("bin/llvm-nm");
            if candidate.is_file() {
                found.push(candidate);
            }
        }
    }
    found
}

/// Parse the LLVM major version out of `llvm-nm --version` output
/// (e.g. "... LLVM version 22.1.2 ..." -> 22). Returns None if the tool
/// can't be run or the output doesn't contain a parsable version.
fn llvm_nm_major_version(path: &Path) -> Option<u32> {
    let output = std::process::Command::new(path).arg("--version").output().ok()?;
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let idx = stdout.find("LLVM version ")?;
    let rest = &stdout[idx + "LLVM version ".len()..];
    let major: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    major.parse().ok()
}

pub(super) fn archive_defined_symbols(path: &Path) -> Option<HashSet<String>> {
    let output = nm_command().arg("-g").arg("--defined-only").arg(path).output();
    let Ok(output) = output else {
        return None;
    };
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let symbols = stdout
        .lines()
        .filter_map(|line| line.split_whitespace().last())
        .filter(|token| !token.ends_with(':'))
        .map(|token| token.trim_start_matches('_').to_string())
        .collect::<HashSet<_>>();
    Some(symbols)
}

pub(crate) fn runtime_archive_has_core_required_symbols(path: &Path) -> bool {
    let Some(symbols) = archive_defined_symbols(path) else {
        return false;
    };
    CORE_REQUIRED_RUNTIME_SYMBOLS
        .iter()
        .all(|symbol| symbols.contains(symbol.trim_start_matches('_')))
}

pub(crate) fn find_abi_complete_simple_core_runtime_library() -> Option<PathBuf> {
    find_simple_core_runtime_library().filter(|path| runtime_archive_has_core_required_symbols(path))
}

/// Find the combined native_all library (runtime + compiler with Cranelift SFFI).
pub(crate) fn find_native_all_library() -> Option<PathBuf> {
    None
}

/// Find the Simple runtime library.
pub(crate) fn find_runtime_library() -> Option<PathBuf> {
    if let Some(dir) = RUNTIME_PATH_OVERRIDE.get() {
        for lane_dir in ["core-c-bootstrap", "core_c_bootstrap"] {
            if let Some(path) = archive_from_dir(&dir.join(lane_dir), "libsimple_runtime") {
                return Some(path);
            }
        }
        if let Some(path) = archive_from_dir(dir, "libsimple_runtime") {
            return Some(path);
        }
    }

    if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
        let p = PathBuf::from(&path);
        for lane_dir in ["core-c-bootstrap", "core_c_bootstrap"] {
            if let Some(found) = archive_from_dir(&p.join(lane_dir), "libsimple_runtime") {
                return Some(found);
            }
        }
        if let Some(found) = archive_from_path_or_dir(&p, "libsimple_runtime") {
            return Some(found);
        }
    }

    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            for lane_dir in ["core-c-bootstrap", "core_c_bootstrap"] {
                if let Some(path) = archive_from_dir(&dir.join(lane_dir), "libsimple_runtime") {
                    return Some(path);
                }
            }
            if let Some(path) = archive_from_dir(dir, "libsimple_runtime") {
                return Some(path);
            }
        }
    }

    None
}

/// Find the compiler-rt builtins archive for a freestanding target.
///
/// Clang reports this through `-print-libgcc-file-name`; on Apple toolchains
/// the returned RISC-V path is a compiler-rt archive under the clang resource
/// directory, while ELF cross toolchains may report libgcc instead.
pub(crate) fn find_compiler_rt_builtins(triple: &str) -> Option<PathBuf> {
    let cc = find_c_compiler();
    let output = std::process::Command::new(&cc)
        .arg(format!("--target={triple}"))
        .arg("-print-libgcc-file-name")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let raw = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if raw.is_empty() {
        return None;
    }
    let path = PathBuf::from(raw);
    if path.exists() && path.is_file() {
        Some(path)
    } else {
        None
    }
}

/// Find an objcopy tool that can handle the host object format.
pub(crate) fn find_objcopy_tool() -> Option<String> {
    for prefix in &[
        "/opt/homebrew/opt/llvm@18/bin",
        "/opt/homebrew/opt/llvm/bin",
        "/usr/local/opt/llvm@18/bin",
        "/usr/local/opt/llvm/bin",
    ] {
        let path = format!("{prefix}/llvm-objcopy");
        if std::path::Path::new(&path).exists() {
            return Some(path);
        }
    }
    if std::process::Command::new("llvm-objcopy")
        .arg("--version")
        .output()
        .is_ok()
    {
        return Some("llvm-objcopy".to_string());
    }
    if std::process::Command::new("objcopy").arg("--version").output().is_ok() {
        return Some("objcopy".to_string());
    }
    None
}

fn canonical_archive_symbol(symbol: &str) -> &str {
    #[cfg(target_os = "macos")]
    {
        symbol.strip_prefix('_').unwrap_or(symbol)
    }
    #[cfg(not(target_os = "macos"))]
    {
        symbol
    }
}

pub(super) fn archive_global_symbols(path: &Path) -> Result<(BTreeMap<String, usize>, BTreeSet<String>), String> {
    let output = nm_command()
        .arg("-g")
        .arg("-p")
        .arg(path)
        .output()
        .map_err(|err| format!("failed to inspect archive {}: {err}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "failed to inspect archive {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }

    let mut defined = BTreeMap::new();
    let mut undefined = BTreeSet::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let (kind, name) = match fields.as_slice() {
            [kind, name] if kind.len() == 1 => (*kind, *name),
            [_address, kind, name] if kind.len() == 1 => (*kind, *name),
            _ => continue,
        };
        if matches!(kind, "U" | "w" | "v") {
            undefined.insert(name.to_string());
        } else {
            *defined.entry(name.to_string()).or_insert(0) += 1;
        }
    }
    Ok((defined, undefined))
}

fn forbidden_archive_sections(path: &Path) -> Result<Vec<&'static str>, String> {
    let tool = find_objdump_tool().ok_or_else(|| {
        format!(
            "cannot verify constructor removal from {}: no objdump/readelf tool found",
            path.display()
        )
    })?;
    let output = if tool.contains("readelf") {
        std::process::Command::new(&tool).arg("-S").arg(path).output()
    } else {
        std::process::Command::new(&tool).arg("-h").arg(path).output()
    }
    .map_err(|err| format!("failed to inspect sections in {}: {err}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "failed to inspect sections in {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    Ok([
        ".init_array",
        ".ctors",
        ".fini_array",
        ".dtors",
        "__mod_init_func",
        "__mod_term_func",
    ]
    .into_iter()
    .filter(|section| stdout.contains(section))
    .collect())
}

#[derive(Clone, Copy)]
enum Stage4CliCUndefinedPolicy {
    Time,
    Sqlite,
    Memtrack,
}

struct Stage4CliCProviderSpec {
    source: &'static str,
    archive: &'static str,
    definitions: &'static [&'static str],
    undefined: Stage4CliCUndefinedPolicy,
}

const STAGE4_C_TIME_DEFINITIONS: &[&str] = &[
    "rt_progress_get_elapsed_seconds",
    "rt_progress_init",
    "rt_progress_reset",
    "rt_time_now_seconds_f64",
    "rt_timestamp_add_days",
    "rt_timestamp_diff_days",
    "rt_timestamp_from_components",
    "rt_timestamp_get_day",
    "rt_timestamp_get_hour",
    "rt_timestamp_get_microsecond",
    "rt_timestamp_get_minute",
    "rt_timestamp_get_month",
    "rt_timestamp_get_second",
    "rt_timestamp_get_year",
];

const STAGE4_C_SQLITE_DEFINITIONS: &[&str] = &[
    "rt_sqlite_begin",
    "rt_sqlite_bind_float",
    "rt_sqlite_bind_int",
    "rt_sqlite_bind_null",
    "rt_sqlite_bind_text",
    "rt_sqlite_changes",
    "rt_sqlite_close",
    "rt_sqlite_column_count",
    "rt_sqlite_column_float",
    "rt_sqlite_column_int",
    "rt_sqlite_column_name",
    "rt_sqlite_column_text",
    "rt_sqlite_column_type",
    "rt_sqlite_commit",
    "rt_sqlite_error_message",
    "rt_sqlite_execute",
    "rt_sqlite_execute_batch",
    "rt_sqlite_finalize",
    "rt_sqlite_last_insert_rowid",
    "rt_sqlite_open",
    "rt_sqlite_open_memory",
    "rt_sqlite_prepare",
    "rt_sqlite_query",
    "rt_sqlite_query_done",
    "rt_sqlite_query_next",
    "rt_sqlite_reset",
    "rt_sqlite_rollback",
];

const STAGE4_C_TIME_UNDEFINED: &[&str] = &["clock_gettime"];

const STAGE4_C_SQLITE_UNDEFINED: &[&str] = &[
    "rt_string_data",
    "rt_string_new",
    "sqlite3_bind_double",
    "sqlite3_bind_int64",
    "sqlite3_bind_null",
    "sqlite3_bind_text",
    "sqlite3_changes",
    "sqlite3_close",
    "sqlite3_column_count",
    "sqlite3_column_double",
    "sqlite3_column_int64",
    "sqlite3_column_name",
    "sqlite3_column_text",
    "sqlite3_column_type",
    "sqlite3_errmsg",
    "sqlite3_exec",
    "sqlite3_finalize",
    "sqlite3_free",
    "sqlite3_last_insert_rowid",
    "sqlite3_open",
    "sqlite3_prepare_v2",
    "sqlite3_reset",
    "sqlite3_step",
];

const STAGE4_C_MEMTRACK_UNDEFINED: &[&str] = &["calloc", "fclose", "fopen", "fprintf", "free"];

const STAGE4_C_MEMTRACK_DEFINITIONS: &[&str] = &[
    "g_memtrack_enabled",
    "spl_memtrack_bytes_since",
    "spl_memtrack_clear_listener",
    "spl_memtrack_count_since",
    "spl_memtrack_disable",
    "spl_memtrack_dump_since",
    "spl_memtrack_enable",
    "spl_memtrack_is_enabled",
    "spl_memtrack_live_bytes",
    "spl_memtrack_live_count",
    "spl_memtrack_record",
    "spl_memtrack_reset",
    "spl_memtrack_set_listener",
    "spl_memtrack_snapshot",
    "spl_memtrack_unrecord",
];

const STAGE4_C_PROVIDER_SPECS: &[Stage4CliCProviderSpec] = &[
    Stage4CliCProviderSpec {
        source: "runtime_timestamp.c",
        archive: "libsimple_stage4_time.a",
        definitions: STAGE4_C_TIME_DEFINITIONS,
        undefined: Stage4CliCUndefinedPolicy::Time,
    },
    Stage4CliCProviderSpec {
        source: "runtime_sqlite.c",
        archive: "libsimple_stage4_sqlite.a",
        definitions: STAGE4_C_SQLITE_DEFINITIONS,
        undefined: Stage4CliCUndefinedPolicy::Sqlite,
    },
    Stage4CliCProviderSpec {
        source: "runtime_memtrack.c",
        archive: "libsimple_stage4_memtrack.a",
        definitions: STAGE4_C_MEMTRACK_DEFINITIONS,
        undefined: Stage4CliCUndefinedPolicy::Memtrack,
    },
];

fn stage4_cli_c_expected_undefined(policy: Stage4CliCUndefinedPolicy) -> &'static [&'static str] {
    match policy {
        Stage4CliCUndefinedPolicy::Time => STAGE4_C_TIME_UNDEFINED,
        Stage4CliCUndefinedPolicy::Sqlite => STAGE4_C_SQLITE_UNDEFINED,
        Stage4CliCUndefinedPolicy::Memtrack => STAGE4_C_MEMTRACK_UNDEFINED,
    }
}

fn stage4_cli_c_provider_spec(source: &str) -> Option<&'static Stage4CliCProviderSpec> {
    STAGE4_C_PROVIDER_SPECS.iter().find(|spec| spec.source == source)
}

fn validate_stage4_cli_c_provider_archive(
    path: &Path,
    spec: &Stage4CliCProviderSpec,
) -> Result<BTreeSet<String>, String> {
    let forbidden_sections = forbidden_archive_sections(path)?;
    if !forbidden_sections.is_empty() {
        return Err(format!(
            "Stage4 C provider {} retained constructor/destructor sections: {}",
            path.display(),
            forbidden_sections.join(", ")
        ));
    }

    let (raw_defined, raw_undefined) = archive_global_symbols(path)?;
    let mut defined = BTreeMap::new();
    for (symbol, count) in raw_defined {
        *defined
            .entry(canonical_archive_symbol(&symbol).to_string())
            .or_insert(0usize) += count;
    }
    let expected: BTreeSet<String> = spec.definitions.iter().map(|symbol| (*symbol).to_string()).collect();
    let actual: BTreeSet<String> = defined.keys().cloned().collect();
    let missing: Vec<&str> = expected.difference(&actual).map(String::as_str).collect();
    let unexpected: Vec<&str> = actual.difference(&expected).map(String::as_str).collect();
    let duplicates: Vec<String> = defined
        .iter()
        .filter(|(_, count)| **count != 1)
        .map(|(symbol, count)| format!("{symbol} ({count})"))
        .collect();
    let actual_undefined: BTreeSet<String> = raw_undefined
        .iter()
        .map(|symbol| canonical_archive_symbol(symbol))
        .map(ToOwned::to_owned)
        .collect();
    let expected_undefined: BTreeSet<String> = stage4_cli_c_expected_undefined(spec.undefined)
        .iter()
        .map(|symbol| (*symbol).to_string())
        .collect();
    let missing_undefined: Vec<&str> = expected_undefined
        .difference(&actual_undefined)
        .map(String::as_str)
        .collect();
    let unexpected_undefined: Vec<&str> = actual_undefined
        .difference(&expected_undefined)
        .map(String::as_str)
        .collect();
    if !missing.is_empty()
        || !unexpected.is_empty()
        || !duplicates.is_empty()
        || !missing_undefined.is_empty()
        || !unexpected_undefined.is_empty()
    {
        return Err(format!(
            "invalid Stage4 C provider {}: missing definitions [{}]; unexpected definitions [{}]; non-single definitions [{}]; missing undefined [{}]; unexpected undefined [{}]",
            path.display(),
            missing.join(", "),
            unexpected.join(", "),
            duplicates.join(", "),
            missing_undefined.join(", "),
            unexpected_undefined.join(", ")
        ));
    }
    Ok(actual)
}

#[cfg(test)]
pub(super) fn validate_stage4_cli_c_provider_archive_contract(path: &Path, source: &str) -> Result<(), String> {
    let spec =
        stage4_cli_c_provider_spec(source).ok_or_else(|| format!("unknown Stage4 C provider source {source}"))?;
    validate_stage4_cli_c_provider_archive(path, spec).map(|_| ())
}

fn archive_definition_owners(archives: &[(&str, &Path)]) -> Result<BTreeMap<String, String>, String> {
    let mut owners = BTreeMap::<String, String>::new();
    for (label, archive) in archives {
        let forbidden_sections = forbidden_archive_sections(archive)?;
        if !forbidden_sections.is_empty() {
            return Err(format!(
                "Stage4 archive {label} retained constructor/destructor sections: {}",
                forbidden_sections.join(", ")
            ));
        }
        let (defined, _) = archive_global_symbols(archive)?;
        if defined.is_empty() {
            return Err(format!("Stage4 archive {label} defines no global symbols"));
        }
        for (raw_symbol, count) in defined {
            let symbol = canonical_archive_symbol(&raw_symbol).to_string();
            if count != 1 {
                return Err(format!("Stage4 archive {label} defines `{symbol}` {count} times"));
            }
            if let Some(first_owner) = owners.insert(symbol.clone(), (*label).to_string()) {
                return Err(format!(
                    "Stage4 archive overlap: `{symbol}` is defined by both {first_owner} and {label}"
                ));
            }
        }
    }
    Ok(owners)
}

fn validate_archive_definition_disjointness(archives: &[(&str, &Path)]) -> Result<(), String> {
    archive_definition_owners(archives).map(|_| ())
}

pub(super) fn validate_requested_symbol_owners(
    archives: &[(&str, &Path)],
    requested_symbols: &[&str],
) -> Result<BTreeMap<String, String>, String> {
    let requested = requested_symbols.iter().copied().collect::<BTreeSet<_>>();
    if requested.is_empty() {
        return Err("Stage4 requested symbol set is empty".to_string());
    }
    let all_owners = archive_definition_owners(archives)?;
    let mut requested_owners = BTreeMap::new();
    let mut missing = Vec::new();
    for symbol in requested {
        if let Some(owner) = all_owners.get(symbol) {
            requested_owners.insert(symbol.to_string(), owner.clone());
        } else {
            missing.push(symbol);
        }
    }
    if !missing.is_empty() {
        return Err(format!(
            "Stage4 requested symbols have no archive owner: {}",
            missing.join(", ")
        ));
    }
    Ok(requested_owners)
}

fn stage4_system_library_path(cc: &str, name: &str) -> Result<PathBuf, String> {
    let output = std::process::Command::new(cc)
        .arg(format!("-print-file-name={name}"))
        .output()
        .map_err(|err| format!("failed to ask target compiler {cc} for {name}: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "target compiler {cc} failed to resolve {name}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let path = PathBuf::from(String::from_utf8_lossy(&output.stdout).trim());
    if path.as_os_str().is_empty() || path.as_path() == Path::new(name) || !path.is_file() {
        return Err(format!("target compiler {cc} did not resolve {name}"));
    }
    Ok(path)
}

fn stage4_shared_library_definitions(path: &Path) -> Result<BTreeSet<String>, String> {
    let output = nm_command()
        .arg("-D")
        .arg("-g")
        .arg("--defined-only")
        .arg(path)
        .output()
        .map_err(|err| format!("failed to inspect system library {}: {err}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "failed to inspect system library {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let mut definitions = BTreeSet::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() < 2 || fields[fields.len() - 2].len() != 1 {
            continue;
        }
        let symbol = canonical_archive_symbol(fields[fields.len() - 1])
            .split('@')
            .next()
            .unwrap_or_default();
        if !symbol.is_empty() {
            definitions.insert(symbol.to_string());
        }
    }
    if definitions.is_empty() {
        return Err(format!(
            "system library {} exposes no readable definitions",
            path.display()
        ));
    }
    Ok(definitions)
}

fn stage4_static_library_definitions(path: &Path) -> Result<BTreeSet<String>, String> {
    let forbidden_sections = forbidden_archive_sections(path)?;
    if !forbidden_sections.is_empty() {
        return Err(format!(
            "static system library {} retained constructor/destructor sections: {}",
            path.display(),
            forbidden_sections.join(", ")
        ));
    }
    let (raw_defined, _) = archive_global_symbols(path)?;
    let duplicates: Vec<&str> = raw_defined
        .iter()
        .filter(|(_, count)| **count != 1)
        .map(|(symbol, _)| symbol.as_str())
        .collect();
    if !duplicates.is_empty() {
        return Err(format!(
            "static system library {} has duplicate global definitions: {}",
            path.display(),
            duplicates.join(", ")
        ));
    }
    let definitions: BTreeSet<String> = raw_defined
        .keys()
        .map(|symbol| {
            canonical_archive_symbol(symbol)
                .split('@')
                .next()
                .unwrap_or_default()
                .to_string()
        })
        .filter(|symbol| !symbol.is_empty())
        .collect();
    if definitions.is_empty() {
        return Err(format!(
            "static system library {} defines no global symbols",
            path.display()
        ));
    }
    Ok(definitions)
}

fn resolve_stage4_system_library(cc: &str, candidates: &[(&str, bool)]) -> Result<(PathBuf, BTreeSet<String>), String> {
    let mut failures: Vec<String> = Vec::new();
    for (name, shared) in candidates {
        let result = (|| {
            let path = stage4_system_library_path(cc, name)?;
            let definitions = if *shared {
                stage4_shared_library_definitions(&path)?
            } else {
                stage4_static_library_definitions(&path)?
            };
            Ok((path, definitions))
        })();
        match result {
            Ok(library) => return Ok(library),
            Err(error) => failures.push(error),
        }
    }
    Err(format!(
        "cannot resolve a clean Stage4 system library: {}",
        failures.join("; ")
    ))
}

fn validate_stage4_system_library_ownership(
    archive: &Path,
    spec: &Stage4CliCProviderSpec,
    library: &Path,
    library_definitions: &BTreeSet<String>,
) -> Result<(), String> {
    let (_, undefined) = archive_global_symbols(archive)?;
    let system_undefined: Vec<&str> = undefined
        .iter()
        .map(|symbol| canonical_archive_symbol(symbol))
        .filter(|symbol| {
            !(matches!(spec.undefined, Stage4CliCUndefinedPolicy::Sqlite)
                && matches!(*symbol, "rt_string_data" | "rt_string_new"))
        })
        .collect();
    let missing: Vec<&str> = system_undefined
        .iter()
        .copied()
        .filter(|symbol| !library_definitions.contains(*symbol))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "Stage4 C provider {} has undefined symbols not owned by {}: {}",
            spec.source,
            library.display(),
            missing.join(", ")
        ));
    }
    Ok(())
}

/// Validate only ABI disjointness for the staged Stage4 C components.
///
/// This deliberately does not select the components or prove that their
/// exports satisfy a complete native-build provider manifest.
pub(crate) fn validate_stage4_cli_c_provider_archive_disjointness(
    core_archive: &Path,
    compiler_archive: &Path,
    provider_archives: &[PathBuf],
) -> Result<(), String> {
    if provider_archives.len() != STAGE4_C_PROVIDER_SPECS.len() {
        return Err(format!(
            "Stage4 C provider disjointness requires exactly {} providers (found {})",
            STAGE4_C_PROVIDER_SPECS.len(),
            provider_archives.len()
        ));
    }
    for (provider, spec) in provider_archives.iter().zip(STAGE4_C_PROVIDER_SPECS) {
        validate_stage4_cli_c_provider_archive(provider, spec)?;
    }
    let (core_defined, _) = archive_global_symbols(core_archive)?;
    for core_symbol in ["rt_string_data", "rt_string_new"] {
        let count: usize = core_defined
            .iter()
            .filter(|(symbol, _)| canonical_archive_symbol(symbol) == core_symbol)
            .map(|(_, count)| *count)
            .sum();
        if count != 1 {
            return Err(format!(
                "Stage4 core must own `{core_symbol}` exactly once for the SQLite provider (found {count})"
            ));
        }
    }
    let mut archives = vec![("core", core_archive), ("compiler", compiler_archive)];
    for (index, provider) in provider_archives.iter().enumerate() {
        archives.push((
            STAGE4_C_PROVIDER_SPECS
                .get(index)
                .map_or("provider", |spec| spec.source),
            provider,
        ));
    }
    validate_archive_definition_disjointness(&archives)
}

/// Build the disabled native GNU/Linux Stage4 C provider components.
///
/// Callers must separately validate requested-owner completeness before these
/// archives may be selected for a link.
pub(crate) fn build_stage4_cli_c_provider_archives(build_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let target = effective_target();
    if !cfg!(all(target_os = "linux", target_env = "gnu"))
        || target.os != simple_common::target::TargetOS::Linux
        || !target.is_host()
    {
        return Err("Stage4 C provider archives currently require the native GNU/Linux host target".to_string());
    }
    let runtime_root = find_core_c_runtime_source_root()
        .ok_or_else(|| "cannot locate src/runtime for Stage4 C providers".to_string())?;
    std::fs::create_dir_all(build_dir).map_err(|err| {
        format!(
            "failed to create Stage4 C provider directory {}: {err}",
            build_dir.display()
        )
    })?;
    let cc = target_c_compiler(target);
    let ar = find_archive_tool();
    let riscv_vector = std::env::var("SIMPLE_RUNTIME_RISCV64_VECTOR").ok().as_deref() == Some("1");
    let mut archives = Vec::new();

    for spec in STAGE4_C_PROVIDER_SPECS {
        let object = build_dir.join(format!(
            "{}.{}",
            spec.source.trim_end_matches(".c"),
            host_object_extension()
        ));
        let archive = build_dir.join(spec.archive);
        let _ = std::fs::remove_file(&object);
        let _ = std::fs::remove_file(&archive);
        let compile = std::process::Command::new(&cc)
            .arg("-c")
            .arg("-Os")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-fno-unwind-tables")
            .arg("-fno-asynchronous-unwind-tables")
            .arg("-fno-stack-protector")
            .arg("-fno-builtin")
            .arg("-fPIC")
            .arg("-std=gnu11")
            .args(core_c_target_flags(target, spec.source, riscv_vector))
            .arg(format!("-I{}", runtime_root.display()))
            .arg(format!("-I{}", runtime_root.join("platform").display()))
            .arg(runtime_root.join(spec.source))
            .arg("-o")
            .arg(&object)
            .output()
            .map_err(|err| format!("failed to compile Stage4 C provider {} with {cc}: {err}", spec.source))?;
        if !compile.status.success() {
            return Err(format!(
                "failed to compile Stage4 C provider {}: {}",
                spec.source,
                String::from_utf8_lossy(&compile.stderr).trim()
            ));
        }
        validate_stage4_cli_c_provider_archive(&object, spec)?;

        let archived = archive_create_command(&ar, &archive, std::slice::from_ref(&object), false, true)
            .output()
            .map_err(|err| format!("failed to execute deterministic archive tool {ar}: {err}"))?;
        if !archived.status.success() {
            return Err(format!(
                "failed to create deterministic Stage4 C provider archive {}: {}",
                archive.display(),
                String::from_utf8_lossy(&archived.stderr).trim()
            ));
        }
        let members = archive_list_command(&ar, &archive).output().map_err(|err| {
            format!(
                "failed to inspect Stage4 C provider archive {}: {err}",
                archive.display()
            )
        })?;
        let member_stdout = String::from_utf8_lossy(&members.stdout);
        let actual_members: Vec<&str> = member_stdout
            .lines()
            .map(str::trim)
            .filter(|member| !member.is_empty())
            .collect();
        let expected_member = object.file_name().and_then(|name| name.to_str()).unwrap_or_default();
        if !members.status.success() || actual_members != [expected_member] {
            return Err(format!(
                "Stage4 C provider archive {} must contain exactly {} (found {})",
                archive.display(),
                expected_member,
                actual_members.join(", ")
            ));
        }
        validate_stage4_cli_c_provider_archive(&archive, spec)?;
        archives.push(archive);
    }

    let labeled: Vec<(&str, &Path)> = STAGE4_C_PROVIDER_SPECS
        .iter()
        .zip(archives.iter())
        .map(|(spec, archive)| (spec.source, archive.as_path()))
        .collect();
    validate_archive_definition_disjointness(&labeled)?;

    let (libc, libc_definitions) = resolve_stage4_system_library(&cc, &[("libc.so.6", true)])?;
    let (sqlite, sqlite_definitions) =
        resolve_stage4_system_library(&cc, &[("libsqlite3.so", true), ("libsqlite3.a", false)])?;
    validate_stage4_system_library_ownership(&archives[0], &STAGE4_C_PROVIDER_SPECS[0], &libc, &libc_definitions)?;
    validate_stage4_system_library_ownership(&archives[1], &STAGE4_C_PROVIDER_SPECS[1], &sqlite, &sqlite_definitions)?;
    validate_stage4_system_library_ownership(&archives[2], &STAGE4_C_PROVIDER_SPECS[2], &libc, &libc_definitions)?;
    Ok(archives)
}

/// Project the exact Stage-4 runtime/provider closure needed by a CLI entry.
///
/// Requested symbols remain global; every other retained definition is local.
/// The result is a deterministic single-member archive with no runtime ABI
/// dependency left unresolved.
pub(crate) fn build_stage4_runtime_capsule_archive(
    core_archive: &Path,
    provider_archives: &[PathBuf],
    requested_symbols: &[String],
    temp_dir: &Path,
) -> Result<PathBuf, String> {
    if provider_archives.len() != STAGE4_C_PROVIDER_SPECS.len() {
        return Err(format!(
            "Stage4 runtime capsule requires exactly {} C providers (found {})",
            STAGE4_C_PROVIDER_SPECS.len(),
            provider_archives.len()
        ));
    }
    for (provider, spec) in provider_archives.iter().zip(STAGE4_C_PROVIDER_SPECS) {
        validate_stage4_cli_c_provider_archive(provider, spec)?;
    }
    let inputs: Vec<(&str, &Path)> = std::iter::once(("core", core_archive))
        .chain(
            STAGE4_C_PROVIDER_SPECS
                .iter()
                .zip(provider_archives)
                .map(|(spec, archive)| (spec.source, archive.as_path())),
        )
        .collect();
    validate_archive_definition_disjointness(&inputs)?;
    project_stage4_archive_closure(
        &inputs.iter().map(|(_, archive)| *archive).collect::<Vec<_>>(),
        requested_symbols,
        &[],
        temp_dir,
        "stage4_runtime_capsule",
    )
}

/// Project the requested Rust runtime exports without exposing the rlib's
/// remaining global ABI. Allowed runtime externals must be supplied by the
/// adjacent exact Stage-4 capsules.
pub(crate) fn build_stage4_rust_runtime_projection_archive(
    rust_runtime_archive: &Path,
    requested_symbols: &[String],
    allowed_external_runtime_symbols: &[String],
    temp_dir: &Path,
) -> Result<PathBuf, String> {
    project_stage4_archive_closure(
        &[rust_runtime_archive],
        requested_symbols,
        allowed_external_runtime_symbols,
        temp_dir,
        "stage4_rust_runtime",
    )
}

fn project_stage4_archive_closure(
    inputs: &[&Path],
    requested_symbols: &[String],
    allowed_external_runtime_symbols: &[String],
    temp_dir: &Path,
    stem: &str,
) -> Result<PathBuf, String> {
    if !cfg!(all(target_os = "linux", target_env = "gnu")) {
        return Err("Stage4 archive projection currently requires native GNU/Linux binutils semantics".to_string());
    }
    let output = temp_dir.join(format!("libsimple_{stem}.a"));
    let closure_object = temp_dir.join(format!("{stem}_closure.o"));
    let localized_object = temp_dir.join(format!("{stem}_local.o"));
    let localize_path = temp_dir.join(format!("{stem}_localize.syms"));
    if inputs.is_empty() {
        return Err("Stage4 archive projection requires at least one input".to_string());
    }
    for input in inputs {
        if safe_canonicalize(input) == safe_canonicalize(&output) {
            return Err("Stage4 projection inputs and output archive must differ".to_string());
        }
    }
    let requested: BTreeSet<String> = requested_symbols.iter().cloned().collect();
    if requested.is_empty() {
        return Err("Stage4 requested symbol set is empty".to_string());
    }
    if requested.len() != requested_symbols.len() {
        return Err("Stage4 requested symbol set contains duplicates".to_string());
    }
    let allowed_external: BTreeSet<String> = allowed_external_runtime_symbols.iter().cloned().collect();
    if let Some(symbol) = allowed_external
        .iter()
        .find(|symbol| !symbol.starts_with("rt_") && !symbol.starts_with("spl_"))
    {
        return Err(format!(
            "Stage4 allowed external `{symbol}` is not a runtime ABI symbol"
        ));
    }

    let _ = std::fs::remove_file(&output);
    let _ = std::fs::remove_file(&closure_object);
    let _ = std::fs::remove_file(&localized_object);
    let _ = std::fs::remove_file(&localize_path);

    let result = (|| {
        let mut root_counts = BTreeMap::<String, usize>::new();
        for input in inputs {
            let (defined, _) = archive_global_symbols(input)?;
            for (raw_symbol, count) in defined {
                let symbol = canonical_archive_symbol(&raw_symbol);
                if requested.contains(symbol) {
                    *root_counts.entry(symbol.to_string()).or_default() += count;
                }
            }
        }
        for symbol in &requested {
            let count = root_counts.get(symbol).copied().unwrap_or_default();
            if count != 1 {
                return Err(format!(
                    "Stage4 projection root `{symbol}` has {count} archive definitions"
                ));
            }
        }

        std::fs::create_dir_all(temp_dir).map_err(|err| {
            format!(
                "failed to create Stage4 runtime capsule directory {}: {err}",
                temp_dir.display()
            )
        })?;
        let cc = find_c_compiler();
        let mut closure_cmd = std::process::Command::new(&cc);
        closure_cmd
            .arg("-nostdlib")
            .arg("-no-pie")
            .arg("-Wl,-r")
            .arg("-Wl,--gc-sections");
        for symbol in &requested {
            closure_cmd.arg(format!("-Wl,--undefined={symbol}"));
        }
        closure_cmd.arg("-Wl,--start-group");
        for archive in inputs {
            closure_cmd.arg(archive);
        }
        let closure = closure_cmd
            .arg("-Wl,--end-group")
            .arg("-o")
            .arg(&closure_object)
            .output()
            .map_err(|err| format!("failed to execute Stage4 runtime capsule closure link with {cc}: {err}"))?;
        if !closure.status.success() {
            return Err(format!(
                "Stage4 runtime capsule closure link failed: {}",
                String::from_utf8_lossy(&closure.stderr).trim()
            ));
        }

        let (closure_defined, closure_undefined) = archive_global_symbols(&closure_object)?;
        for symbol in &requested {
            let count: usize = closure_defined
                .iter()
                .filter(|(raw, _)| canonical_archive_symbol(raw) == symbol)
                .map(|(_, count)| *count)
                .sum();
            if count != 1 {
                return Err(format!(
                    "Stage4 runtime capsule root `{symbol}` has {count} definitions"
                ));
            }
        }
        let unresolved_runtime: Vec<&str> = closure_undefined
            .iter()
            .map(|symbol| canonical_archive_symbol(symbol))
            .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
            .filter(|symbol| !allowed_external.contains(*symbol))
            .collect();
        if !unresolved_runtime.is_empty() {
            return Err(format!(
                "Stage4 runtime capsule has unresolved runtime symbols: {}",
                unresolved_runtime.join(", ")
            ));
        }

        let localize_text = closure_defined
            .keys()
            .filter(|raw| !requested.contains(canonical_archive_symbol(raw)))
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(
            &localize_path,
            if localize_text.is_empty() {
                String::new()
            } else {
                localize_text + "\n"
            },
        )
        .map_err(|err| format!("failed to write Stage4 runtime capsule localization list: {err}"))?;

        let objcopy = find_objcopy_tool().ok_or_else(|| "Stage4 runtime capsule requires objcopy".to_string())?;
        let localized = std::process::Command::new(&objcopy)
            .arg(format!("--localize-symbols={}", localize_path.display()))
            .arg("--remove-section=.init_array")
            .arg("--remove-section=.init_array.*")
            .arg("--remove-section=.ctors")
            .arg("--remove-section=.ctors.*")
            .arg("--remove-section=.fini_array")
            .arg("--remove-section=.fini_array.*")
            .arg("--remove-section=.dtors")
            .arg("--remove-section=.dtors.*")
            .arg("--remove-section=__mod_init_func")
            .arg("--remove-section=__mod_term_func")
            .arg(&closure_object)
            .arg(&localized_object)
            .output()
            .map_err(|err| format!("failed to execute Stage4 runtime capsule objcopy: {err}"))?;
        if !localized.status.success() {
            return Err(format!(
                "Stage4 runtime capsule objcopy failed: {}",
                String::from_utf8_lossy(&localized.stderr).trim()
            ));
        }

        let (localized_defined, localized_undefined) = archive_global_symbols(&localized_object)?;
        let actual: BTreeMap<String, usize> = localized_defined
            .iter()
            .map(|(symbol, count)| (canonical_archive_symbol(symbol).to_string(), *count))
            .collect();
        let expected: BTreeMap<String, usize> = requested.iter().map(|symbol| (symbol.clone(), 1)).collect();
        if actual != expected {
            return Err(format!(
                "Stage4 runtime capsule globals differ from requested roots: expected {expected:?}, found {actual:?}"
            ));
        }
        let unresolved_runtime: Vec<&str> = localized_undefined
            .iter()
            .map(|symbol| canonical_archive_symbol(symbol))
            .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
            .filter(|symbol| !allowed_external.contains(*symbol))
            .collect();
        if !unresolved_runtime.is_empty() {
            return Err(format!(
                "Stage4 runtime capsule has unresolved runtime symbols after localization: {}",
                unresolved_runtime.join(", ")
            ));
        }
        let forbidden_sections = forbidden_archive_sections(&localized_object)?;
        if !forbidden_sections.is_empty() {
            return Err(format!(
                "Stage4 runtime capsule retained constructor/destructor sections: {}",
                forbidden_sections.join(", ")
            ));
        }

        let ar = find_archive_tool();
        let archived = archive_create_command(&ar, &output, std::slice::from_ref(&localized_object), false, true)
            .output()
            .map_err(|err| format!("failed to execute deterministic archive tool {ar}: {err}"))?;
        if !archived.status.success() {
            return Err(format!(
                "failed to create Stage4 runtime capsule archive: {}",
                String::from_utf8_lossy(&archived.stderr).trim()
            ));
        }
        let members = archive_list_command(&ar, &output)
            .output()
            .map_err(|err| format!("failed to inspect Stage4 runtime capsule archive members: {err}"))?;
        let member_stdout = String::from_utf8_lossy(&members.stdout);
        let member_names: Vec<&str> = member_stdout
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .collect();
        let expected_member = format!("{stem}_local.o");
        if !members.status.success() || member_names != [expected_member.as_str()] {
            return Err(format!(
                "Stage4 projection archive must contain exactly {expected_member} (found {})",
                member_names.join(", ")
            ));
        }
        let (output_defined, output_undefined) = archive_global_symbols(&output)?;
        if output_defined != localized_defined || output_undefined != localized_undefined {
            return Err("Stage4 runtime capsule symbol table changed while archiving".to_string());
        }
        let output_sections = forbidden_archive_sections(&output)?;
        if !output_sections.is_empty() {
            return Err(format!(
                "Stage4 runtime capsule archive retained constructor/destructor sections: {}",
                output_sections.join(", ")
            ));
        }
        Ok(output.clone())
    })();

    let _ = std::fs::remove_file(&closure_object);
    let _ = std::fs::remove_file(&localized_object);
    let _ = std::fs::remove_file(&localize_path);
    if result.is_err() {
        let _ = std::fs::remove_file(&output);
    }
    result
}

/// Build the Stage-4 compiler hook archive without importing a second runtime.
///
/// The dedicated archive's globally defined `rt_cranelift_*` symbols are the
/// exact export contract. On GNU/Linux, a relocatable link roots those exports
/// and section-GCs everything outside their dependency closure. Surviving
/// non-contract definitions are localized; the result is rejected unless its
/// public ABI is contract-only and disjoint from every provider.
pub(crate) fn build_compiler_backfill_archive(
    compiler_archive: &Path,
    provider_archives: &[PathBuf],
    temp_dir: &Path,
) -> Result<PathBuf, String> {
    if !cfg!(target_os = "linux") {
        return Err("compiler backfill closure currently requires GNU/Linux binutils semantics".to_string());
    }

    let output = temp_dir.join("libsimple_compiler_backfill.a");
    if safe_canonicalize(compiler_archive) == safe_canonicalize(&output) {
        return Err("compiler backfill input and output archive must differ".to_string());
    }
    let closure_object = temp_dir.join("compiler_backfill_closure.o");
    let localized_object = temp_dir.join("compiler_backfill_local.o");
    let localize_path = temp_dir.join("compiler_backfill_localize.syms");
    let _ = std::fs::remove_file(&output);
    let _ = std::fs::remove_file(&closure_object);
    let _ = std::fs::remove_file(&localized_object);
    let _ = std::fs::remove_file(&localize_path);

    let result = (|| {
        let (source_defined, source_undefined) = archive_global_symbols(compiler_archive)?;
        if source_defined.is_empty() {
            return Err(format!(
                "compiler archive {} defines no global symbols",
                compiler_archive.display()
            ));
        }

        let mut contract_counts = BTreeMap::new();
        let mut manifest_raw = BTreeSet::new();
        for (symbol, count) in &source_defined {
            let canonical = canonical_archive_symbol(symbol);
            if canonical.starts_with("rt_cranelift_") {
                *contract_counts.entry(canonical.to_string()).or_insert(0usize) += *count;
                manifest_raw.insert(symbol.clone());
            }
        }
        if contract_counts.is_empty() {
            return Err(format!(
                "dedicated compiler backfill archive {} defines no rt_cranelift_* exports",
                compiler_archive.display()
            ));
        }
        for (export, count) in &contract_counts {
            if *count != 1 {
                return Err(format!(
                    "derived compiler backfill export `{export}` must be defined exactly once in {} (found {count})",
                    compiler_archive.display()
                ));
            }
        }
        let manifest: BTreeSet<String> = contract_counts.into_keys().collect();

        let forbidden_source_runtime: BTreeSet<&str> = source_defined
            .keys()
            .chain(source_undefined.iter())
            .map(|symbol| canonical_archive_symbol(symbol))
            .filter(|symbol| (symbol.starts_with("rt_") || symbol.starts_with("spl_")) && !manifest.contains(*symbol))
            .collect();
        if !forbidden_source_runtime.is_empty() {
            return Err(format!(
                "compiler backfill source contains runtime/provider ownership outside the manifest: {}",
                forbidden_source_runtime.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }

        std::fs::create_dir_all(temp_dir).map_err(|err| {
            format!(
                "failed to create compiler backfill directory {}: {err}",
                temp_dir.display()
            )
        })?;
        let cc = find_c_compiler();
        let mut closure_cmd = std::process::Command::new(&cc);
        closure_cmd
            .arg("-nostdlib")
            .arg("-no-pie")
            .arg("-Wl,-r")
            .arg("-Wl,--gc-sections");
        for export in &manifest {
            closure_cmd.arg(format!("-Wl,--undefined={export}"));
        }
        let closure_result = closure_cmd
            .arg("-o")
            .arg(&closure_object)
            .arg(compiler_archive)
            .output()
            .map_err(|err| format!("failed to execute compiler backfill closure link with {cc}: {err}"))?;
        if !closure_result.status.success() {
            return Err(format!(
                "compiler backfill closure link failed: {}",
                String::from_utf8_lossy(&closure_result.stderr).trim()
            ));
        }

        let (closure_defined, closure_undefined) = archive_global_symbols(&closure_object)?;
        for export in &manifest {
            let count: usize = closure_defined
                .iter()
                .filter(|(symbol, _)| canonical_archive_symbol(symbol) == export)
                .map(|(_, count)| *count)
                .sum();
            if count != 1 {
                return Err(format!(
                    "compiler backfill closure export `{export}` has {count} definitions"
                ));
            }
        }
        let forbidden_closure_runtime: Vec<&str> = closure_undefined
            .iter()
            .map(|symbol| canonical_archive_symbol(symbol))
            .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
            .collect();
        if !forbidden_closure_runtime.is_empty() {
            return Err(format!(
                "compiler backfill closure has forbidden runtime/provider dependencies: {}",
                forbidden_closure_runtime.join(", ")
            ));
        }

        let localize_symbols: Vec<&String> = closure_defined
            .keys()
            .filter(|symbol| !manifest_raw.contains(*symbol))
            .collect();
        let localize_text = localize_symbols
            .iter()
            .map(|symbol| symbol.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::write(
            &localize_path,
            if localize_text.is_empty() {
                String::new()
            } else {
                localize_text + "\n"
            },
        )
        .map_err(|err| format!("failed to write compiler backfill localization list: {err}"))?;

        let objcopy = find_objcopy_tool().ok_or_else(|| "compiler backfill requires objcopy".to_string())?;
        let command_output = std::process::Command::new(&objcopy)
            .arg(format!("--localize-symbols={}", localize_path.display()))
            .arg("--remove-section=.init_array")
            .arg("--remove-section=.init_array.*")
            .arg("--remove-section=.ctors")
            .arg("--remove-section=.ctors.*")
            .arg("--remove-section=.fini_array")
            .arg("--remove-section=.fini_array.*")
            .arg("--remove-section=.dtors")
            .arg("--remove-section=.dtors.*")
            .arg("--remove-section=__mod_init_func")
            .arg("--remove-section=__mod_term_func")
            .arg(&closure_object)
            .arg(&localized_object)
            .output()
            .map_err(|err| format!("failed to execute compiler backfill objcopy: {err}"))?;
        if !command_output.status.success() {
            return Err(format!(
                "compiler backfill objcopy failed: {}",
                String::from_utf8_lossy(&command_output.stderr).trim()
            ));
        }

        let (localized_defined, localized_undefined) = archive_global_symbols(&localized_object)?;
        for export in &manifest {
            let count: usize = localized_defined
                .iter()
                .filter(|(symbol, _)| canonical_archive_symbol(symbol) == export)
                .map(|(_, count)| *count)
                .sum();
            if count != 1 {
                return Err(format!(
                    "localized compiler backfill export `{export}` has {count} definitions"
                ));
            }
        }
        for symbol in localized_defined.keys() {
            let canonical = canonical_archive_symbol(symbol);
            if !manifest.contains(canonical) {
                return Err(format!(
                    "compiler backfill retained unexpected global export `{canonical}`"
                ));
            }
        }
        let forbidden_undefined: Vec<&str> = localized_undefined
            .iter()
            .map(|symbol| canonical_archive_symbol(symbol))
            .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
            .collect();
        if !forbidden_undefined.is_empty() {
            return Err(format!(
                "compiler backfill has forbidden runtime/provider dependencies: {}",
                forbidden_undefined.join(", ")
            ));
        }

        let output_symbols: BTreeSet<String> = localized_defined
            .keys()
            .map(|symbol| canonical_archive_symbol(symbol).to_string())
            .collect();
        for provider in provider_archives {
            let (provider_defined, _) = archive_global_symbols(provider)?;
            if provider_defined.is_empty() {
                return Err(format!(
                    "provider archive {} defines no global symbols",
                    provider.display()
                ));
            }
            let overlap: Vec<String> = provider_defined
                .keys()
                .map(|symbol| canonical_archive_symbol(symbol))
                .filter(|symbol| output_symbols.contains(*symbol))
                .map(str::to_string)
                .collect();
            if !overlap.is_empty() {
                return Err(format!(
                    "compiler backfill overlaps provider archive {}: {}",
                    provider.display(),
                    overlap.join(", ")
                ));
            }
        }

        let forbidden_sections = forbidden_archive_sections(&localized_object)?;
        if !forbidden_sections.is_empty() {
            return Err(format!(
                "compiler backfill retained constructor/destructor sections: {}",
                forbidden_sections.join(", ")
            ));
        }

        let archive_tool = find_archive_tool();
        let archive_result = archive_create_command(
            &archive_tool,
            &output,
            std::slice::from_ref(&localized_object),
            false,
            true,
        )
        .output()
        .map_err(|err| format!("failed to execute deterministic archive tool {archive_tool}: {err}"))?;
        if !archive_result.status.success() {
            return Err(format!(
                "failed to create compiler backfill archive: {}",
                String::from_utf8_lossy(&archive_result.stderr).trim()
            ));
        }
        let members = archive_list_command(&archive_tool, &output)
            .output()
            .map_err(|err| format!("failed to inspect compiler backfill archive members: {err}"))?;
        let member_stdout = String::from_utf8_lossy(&members.stdout);
        let member_names: Vec<&str> = member_stdout.lines().filter(|line| !line.trim().is_empty()).collect();
        if !members.status.success() || member_names != ["compiler_backfill_local.o"] {
            return Err(format!(
                "compiler backfill archive must contain exactly compiler_backfill_local.o (found {})",
                member_names.join(", ")
            ));
        }
        let (output_defined, output_undefined) = archive_global_symbols(&output)?;
        if output_defined != localized_defined || output_undefined != localized_undefined {
            return Err("compiler backfill archive symbol table changed while archiving".to_string());
        }
        let output_sections = forbidden_archive_sections(&output)?;
        if !output_sections.is_empty() {
            return Err(format!(
                "compiler backfill archive retained constructor/destructor sections: {}",
                output_sections.join(", ")
            ));
        }
        Ok(output.clone())
    })();

    let _ = std::fs::remove_file(&closure_object);
    let _ = std::fs::remove_file(&localized_object);
    let _ = std::fs::remove_file(&localize_path);
    if result.is_err() {
        let _ = std::fs::remove_file(&output);
    }
    result
}

/// Error type for LLVM constructor stripping failures (LIM-010).
#[derive(Debug)]
pub(crate) enum StripError {
    ObjcopyNotFound,
    ObjcopyFailed { exit_code: Option<i32>, stderr: String },
    VerificationFailed { sections: Vec<String> },
}

/// Find an objdump (or llvm-objdump) tool for archive verification.
fn find_objdump_tool() -> Option<String> {
    for prefix in &[
        "/opt/homebrew/opt/llvm@18/bin",
        "/opt/homebrew/opt/llvm/bin",
        "/usr/local/opt/llvm@18/bin",
        "/usr/local/opt/llvm/bin",
    ] {
        let path = format!("{prefix}/llvm-objdump");
        if std::path::Path::new(&path).exists() {
            return Some(path);
        }
    }
    if std::process::Command::new("llvm-objdump")
        .arg("--version")
        .output()
        .is_ok()
    {
        return Some("llvm-objdump".to_string());
    }
    // Fall back to readelf which is more commonly available on Linux
    if std::process::Command::new("readelf").arg("--version").output().is_ok() {
        return Some("readelf".to_string());
    }
    if std::process::Command::new("objdump").arg("--version").output().is_ok() {
        return Some("objdump".to_string());
    }
    None
}

/// Verify that a stripped archive has no `.init_array` or `.ctors` sections remaining.
fn verify_stripped_archive(archive_path: &Path) -> Result<(), StripError> {
    let tool = match find_objdump_tool() {
        Some(t) => t,
        None => return Ok(()), // Can't verify without a tool — assume success
    };

    let output = if tool.contains("readelf") {
        std::process::Command::new(&tool).arg("-S").arg(archive_path).output()
    } else {
        std::process::Command::new(&tool).arg("-h").arg(archive_path).output()
    };

    let output = match output {
        Ok(o) => o,
        Err(_) => return Ok(()), // Tool failed to run — assume success
    };

    let stdout = String::from_utf8_lossy(&output.stdout);
    let fields: Vec<&str> = stdout.split_whitespace().collect();
    let forbidden = [".init_array", ".ctors", ".fini_array", ".dtors"];
    let remaining: Vec<String> = forbidden
        .iter()
        .filter(|sec| fields.contains(sec))
        .map(|sec| sec.to_string())
        .collect();

    if remaining.is_empty() {
        Ok(())
    } else {
        Err(StripError::VerificationFailed { sections: remaining })
    }
}

/// Strip LLVM static constructors from a static archive to prevent segfaults (LIM-010).
///
/// Uses `llvm-objcopy` directly on the archive file to remove constructor/destructor
/// sections from every member, preserving duplicate-named members (e.g. multiple
/// `Error.cpp.o`) that `ar x` would silently overwrite.
pub(crate) fn strip_llvm_constructors(lib: &Path, temp_dir: &Path) -> Result<PathBuf, StripError> {
    let objcopy = match find_objcopy_tool() {
        Some(cmd) => cmd,
        None => return Err(StripError::ObjcopyNotFound),
    };

    let archive_path = safe_canonicalize(lib);
    let filtered = temp_dir.join("libsimple_native_all_stripped.a");

    let mut cmd = std::process::Command::new(&objcopy);
    // Keep priority-tagged runtime constructors (for example Rust's
    // `.init_array.00099`); they are not LLVM's plain global ctor section.
    cmd.arg("--remove-section=.init_array")
        .arg("--remove-section=.ctors")
        .arg("--remove-section=.fini_array")
        .arg("--remove-section=.dtors");
    // NOTE(2026-04-15): we deliberately do NOT strip __DATA,__mod_init_func /
    // __mod_term_func on macOS even though LIM-010 (LLVM static constructor
    // segfault) used to require it. ObjC class registration also lives in
    // __mod_init_func, and stripping it leaves NSApplication / NSWindow
    // un-registered, so the first AppKit method dispatch goes through the
    // forwarding path and crashes inside dyld with a NULL selector name (see
    // crash analysis in src/runtime/hosted/cocoa.rs comments). LIM-010 only
    // affects the LLVM backend, which is opt-in via `--backend=llvm-lib`.
    cmd.arg(&archive_path).arg(&filtered);

    let output = cmd.output().map_err(|e| StripError::ObjcopyFailed {
        exit_code: None,
        stderr: format!("failed to execute objcopy: {e}"),
    })?;
    if !output.status.success() {
        return Err(StripError::ObjcopyFailed {
            exit_code: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        });
    }

    verify_stripped_archive(&filtered)?;

    Ok(filtered)
}

/// Check if a mangled symbol name refers to a C standard library / system function.
#[cfg(any(
    target_os = "android",
    target_os = "ios",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "linux",
    target_os = "windows"
))]
pub(crate) fn is_system_symbol(sym: &str) -> bool {
    #[cfg(target_os = "windows")]
    {
        let name = sym.strip_prefix('_').unwrap_or(sym);
        return is_windows_system_name(sym)
            || is_windows_system_name(name)
            || is_windows_system_prefix(sym)
            || is_windows_system_prefix(name);
    }
    #[cfg(not(target_os = "windows"))]
    {
        let name = sym.strip_prefix('_').unwrap_or(sym);
        let versionless = sym.split('@').next().unwrap_or(sym);
        let versionless_name = name.split('@').next().unwrap_or(name);
        if is_known_system_name(sym)
            || is_known_system_name(name)
            || is_known_system_name(versionless)
            || is_known_system_name(versionless_name)
        {
            return true;
        }
        if cfg!(target_os = "macos") {
            return is_macos_system_symbol(sym);
        }
        false
    }
}

/// Return true for libgcc/compiler-rt low-level helper names.
///
/// Freestanding links must resolve these from compiler-rt/libgcc, not from the
/// weak unresolved-symbol stubs. Stubbing these would make RV32 soft-float
/// programs link while producing incorrect arithmetic at runtime.
pub(crate) fn is_compiler_rt_builtin_symbol(sym: &str) -> bool {
    let name = sym.strip_prefix('_').unwrap_or(sym);
    if !sym.starts_with("__") && !name.starts_with("__") {
        return false;
    }
    let builtin_prefixes = [
        "__add",
        "__sub",
        "__mul",
        "__div",
        "__mod",
        "__udiv",
        "__umod",
        "__udivmod",
        "__ashl",
        "__ashr",
        "__lshr",
        "__cmp",
        "__ucmp",
        "__neg",
        "__clz",
        "__ctz",
        "__popcount",
        "__parity",
        "__bswap",
        "__fix",
        "__fixuns",
        "__float",
        "__floatun",
        "__extend",
        "__trunc",
        "__eq",
        "__ne",
        "__lt",
        "__le",
        "__gt",
        "__ge",
        "__unord",
        "__powi",
        "__multi3",
    ];
    builtin_prefixes
        .iter()
        .any(|prefix| sym.starts_with(prefix) || name.starts_with(prefix))
}

#[cfg(target_os = "windows")]
fn is_windows_system_name(name: &str) -> bool {
    matches!(
        name,
        "malloc"
            | "_GLOBAL_OFFSET_TABLE_"
            | "calloc"
            | "realloc"
            | "free"
            | "aligned_alloc"
            | "posix_memalign"
            | "memcpy"
            | "memmove"
            | "memset"
            | "memcmp"
            | "memchr"
            | "strlen"
            | "strcmp"
            | "strncmp"
            | "strcpy"
            | "strncpy"
            | "strcat"
            | "strdup"
            | "strerror"
            | "strstr"
            | "strchr"
            | "strrchr"
            | "strtol"
            | "strtoul"
            | "strtod"
            | "printf"
            | "fprintf"
            | "sprintf"
            | "snprintf"
            | "puts"
            | "fputs"
            | "fputc"
            | "fwrite"
            | "fread"
            | "fopen"
            | "fclose"
            | "fflush"
            | "fgetc"
            | "fgets"
            | "fseek"
            | "ftell"
            | "open"
            | "read"
            | "write"
            | "close"
            | "mkdir"
            | "remove"
            | "rename"
            | "rewind"
            // Objective-C runtime / Darwin libc names may appear in
            // cross-platform unresolved-symbol scans; never synthesize stubs
            // for these ABI-owned symbols on non-Darwin hosts.
            | "class_addMethod"
            | "ivar_getName"
            | "method_getImplementation"
            | "protocol_getName"
            | "stat"
            | "strtoll"
            | "_lseeki64"
            | "exit"
            | "_exit"
            | "abort"
            | "atexit"
            | "getenv"
            | "system"
            | "sqrt"
            | "sqrtf"
            | "sin"
            | "sinf"
            | "cos"
            | "cosf"
            | "tan"
            | "tanf"
            | "acos"
            | "acosf"
            | "asin"
            | "asinf"
            | "atan"
            | "atan2"
            | "atan2f"
            | "atanf"
            | "cbrt"
            | "cbrtf"
            | "cosh"
            | "coshf"
            | "exp"
            | "expf"
            | "fma"
            | "fmaf"
            | "log"
            | "log10"
            | "log10f"
            | "log2"
            | "log2f"
            | "logf"
            | "pow"
            | "powf"
            | "fabs"
            | "fabsf"
            | "ceil"
            | "ceilf"
            | "floor"
            | "floorf"
            | "round"
            | "roundf"
            | "fmod"
            | "fmodf"
            | "sinh"
            | "sinhf"
            | "tanh"
            | "tanhf"
            | "trunc"
            | "truncf"
            | "_hypot"
            | "qsort"
            | "bsearch"
            | "abs"
            | "labs"
            | "rand"
            | "srand"
            | "isdigit"
            | "isalpha"
            | "isspace"
            | "tolower"
            | "toupper"
            | "setlocale"
            | "time"
            | "clock"
            | "__security_cookie"
            | "__security_check_cookie"
            | "__GSHandlerCheck"
            | "___chkstk_ms"
            | "__main"
            | "__popcountdi2"
            | "__acrt_iob_func"
            | "__stdio_common_vfprintf"
            | "__stdio_common_vsprintf"
            | "clock_gettime"
            | "_CxxThrowException"
            | "__CxxFrameHandler3"
            | "_tls_index"
            | "_tls_used"
            | "AddVectoredExceptionHandler"
            | "AssignProcessToJobObject"
            | "BCryptGenRandom"
            | "CancelIo"
            | "CloseHandle"
            | "CoCreateGuid"
            | "CoTaskMemFree"
            | "CompareStringOrdinal"
            | "CreateFileMappingW"
            | "DeviceIoControl"
            | "DiscardVirtualMemory"
            | "DuplicateHandle"
            | "FlushFileBuffers"
            | "FlushViewOfFile"
            | "FormatMessageW"
            | "FreeEnvironmentStringsW"
            | "GetConsoleMode"
            | "GetCurrentProcess"
            | "GetLogicalProcessorInformation"
            | "GetSystemInfo"
            | "LoadLibraryA"
            | "LoadLibraryExA"
            | "LoadLibraryW"
            | "LockFileEx"
            | "MapViewOfFile"
            | "Module32FirstW"
            | "Module32NextW"
            | "PrefetchVirtualMemory"
            | "QueryPerformanceCounter"
            | "QueryPerformanceFrequency"
            | "ReadFile"
            | "ReadFileEx"
            | "RoOriginateErrorW"
            | "SHGetKnownFolderPath"
            | "SetConsoleMode"
            | "SystemFunction036"
            | "UnmapViewOfFile"
            | "VirtualProtect"
            | "lstrlenW"
    )
}

#[cfg(target_os = "windows")]
fn is_windows_system_prefix(name: &str) -> bool {
    name.starts_with("__imp_")
        || name.starts_with("__mingw_")
        || name.starts_with("__p__")
        || name.starts_with("__std_")
        || name.starts_with("__acrt_")
        || name.starts_with("__stdio_common_")
        || name.starts_with("__security_")
        || name.starts_with("__Cxx")
        || name.starts_with("_Cxx")
        || name.starts_with("_tls_")
        || name.starts_with("_Z")
        || name.starts_with("__Z")
        || name.starts_with("Rtl")
        || name.starts_with("Nt")
        || name.starts_with("Get")
        || name.starts_with("Set")
        || name.starts_with("Create")
        || name.starts_with("Close")
        || name.starts_with("Delete")
        || name.starts_with("Duplicate")
        || name.starts_with("Flush")
        || name.starts_with("Map")
        || name.starts_with("Unmap")
        || name.starts_with("Virtual")
        || name.starts_with("Wait")
        || name.starts_with("WideChar")
        || name.starts_with("MultiByte")
        || name.starts_with("Heap")
        || name.starts_with("Local")
        || name.starts_with("SH")
        || name.starts_with("PropVariant")
        || name.starts_with("Variant")
        || name.starts_with("WSA")
}

fn is_macos_system_symbol(sym: &str) -> bool {
    // macOS ABI-variant suffixes (`realpath$DARWIN_EXTSN`, `fopen$UNIX2003`, ...) alias
    // the plain libc entry point; classify them by their base name.
    let sym = sym.split('$').next().unwrap_or(sym);
    let name = sym.strip_prefix('_').unwrap_or(sym);

    // After stripping the `$`-variant suffix, re-check the shared libc/libm table so
    // ABI-variant aliases (e.g. `realpath$DARWIN_EXTSN`) resolve to their base entry.
    if is_known_system_name(sym) || is_known_system_name(name) {
        return true;
    }

    if matches!(
        name,
        "__stderrp" | "__stdinp" | "__stdoutp" | "_stderrp" | "_stdinp" | "_stdoutp"
    ) {
        return true;
    }

    if name.starts_with("_Z")
        || name.starts_with("__Z")
        || name.starts_with("_ZN")
        || name.starts_with("_ZT")
        || name.starts_with("_ZS")
        || name.starts_with("__cxa_")
        || name.starts_with("__cxx")
    {
        return true;
    }

    if name.starts_with("objc_")
        || name.starts_with("_objc_")
        || name.starts_with("OBJC_")
        || name.starts_with("class_")
        || name.starts_with("ivar_")
        || name.starts_with("method_")
        || name.starts_with("protocol_")
    {
        return true;
    }

    if name.starts_with("CF")
        || name.starts_with("kCF")
        || name.starts_with("CC")
        || name.starts_with("Sec")
        || name.starts_with("kSec")
        || name.starts_with("IORegistr")
        || name.starts_with("IOService")
        || name.starts_with("IOObject")
        || name.starts_with("SCDynamic")
        || name.starts_with("SCNetwork")
        || name.starts_with("kSC")
        || name.starts_with("NSApp")
        || name.starts_with("NSView")
        || name.starts_with("NSWindow")
        || name.starts_with("NSFile")
        || name.starts_with("NSKey")
        || name.starts_with("NSConcrete")
        || name.starts_with("_NSGet")
        || name.starts_with("_NSConcrete")
        || name.starts_with("dispatch_")
        || name.starts_with("_dispatch_")
        || name.starts_with("xpc_")
        || name.starts_with("notify_")
        || name.starts_with("os_log")
        || name.starts_with("Block_")
        || name.starts_with("_Block_")
    {
        return true;
    }

    if matches!(
        name,
        "arc4random"
            | "arc4random_buf"
            | "arc4random_uniform"
            | "__error"
            | "__maskrune"
            | "__tolower"
            | "__toupper"
            | "_NSGetExecutablePath"
            | "_NSGetEnviron"
            | "_NSGetArgc"
            | "_NSGetArgv"
            | "__NSConcreteStackBlock"
            | "__NSConcreteGlobalBlock"
            | "os_unfair_lock_lock"
            | "os_unfair_lock_unlock"
            | "mach_absolute_time"
            | "mach_timebase_info"
            | "mach_task_self_"
            | "vm_allocate"
            | "vm_deallocate"
            | "kevent"
            | "kqueue"
            | "pipe2"
            | "flock"
            | "ftruncate"
            | "pread"
            | "pwrite"
            | "writev"
            | "readv"
            | "getifaddrs"
            | "freeifaddrs"
            | "if_nametoindex"
            | "sysctl"
            | "sysctlbyname"
            | "proc_pidpath"
            | "issetugid"
            | "sandbox_check"
            | "cfgetispeed"
            | "cfgetospeed"
            | "clock_getres"
            | "clock_settime"
            | "fsetattrlist"
            | "setattrlist"
            | "getegid"
            | "getgid"
            | "getpeereid"
            | "mkfifo"
            | "recvmsg"
            | "sendfile"
            | "sendmsg"
            | "sigaltstack"
            | "sigdelset"
            | "sigismember"
            | "socketpair"
    ) {
        return true;
    }

    if name.starts_with("pthread_") || name.starts_with("dispatch_") || name.starts_with("mach_") {
        return true;
    }

    // Symbols provided by the C libraries linked alongside `libsimple_native_all.a`
    // (see `PlatformLinkConfig::macos()` / `macos_frameworks()`): libffi, libedit,
    // zlib/zstd, libxml2, libncurses/terminfo, libobjc, plus low-level runtime/dyld/
    // TLS/unwind helpers from libSystem. These resolve from the real `-l`/`-framework`
    // flags at link time, so they must not be weak-stubbed (stubbing wins over the real
    // definition and produces a broken binary).
    if name.starts_with("ffi_")          // libffi
        || name.starts_with("el_")       // libedit
        || name.starts_with("history")   // libedit
        || name.starts_with("tok_")      // libedit
        || name.starts_with("xml")       // libxml2
        || name.starts_with("ZSTD_")     // zstd
        || name.starts_with("MTL")       // Metal framework
        || name.starts_with("Unwind_")   // libunwind / libSystem
        || name.starts_with("_Unwind_")
        || name.starts_with("dyld_")     // dyld image introspection
        || name.starts_with("_dyld_")
        || name.starts_with("tlv_")      // thread-local-variable runtime
        || name.starts_with("_tlv_")
    {
        return true;
    }

    // libz (zlib) and libncurses/terminfo entry points (no common prefix).
    if matches!(
        name,
        // zlib
        "compress" | "compress2" | "compressBound" | "uncompress" | "crc32" | "crc32_combine"
            | "adler32" | "adler32_combine" | "deflate" | "deflateInit_" | "deflateInit2_"
            | "deflateEnd" | "deflateBound" | "inflate" | "inflateInit_" | "inflateInit2_"
            | "inflateEnd" | "zlibVersion"
            // libncurses / terminfo (used transitively by libedit)
            | "setupterm" | "del_curterm" | "set_curterm" | "tigetnum" | "tigetstr" | "tigetflag"
            | "tparm" | "tputs"
            // libobjc runtime (also reachable via Foundation framework)
            | "class_getName" | "class_isMetaClass" | "object_getClass" | "sel_getName"
            | "sel_registerName" | "objc_msgSend" | "objc_getClass" | "objc_lookUpClass"
            // libiconv
            | "iconv" | "iconv_open" | "iconv_close"
    ) {
        return true;
    }

    // Additional libc / libm / libSystem entry points referenced by the combined
    // archive that are missing from `is_known_system_name` above. All resolve from
    // `-lSystem` (already in the macOS lib list); they only need to be kept out of the
    // stub set so the real definitions win.
    if matches!(
        name,
        // libm
        "cbrt" | "cbrtf" | "cosh" | "sinh" | "tanh" | "exp2" | "exp2f" | "exp10" | "_exp10"
            | "hypot" | "hypotf" | "ldexp" | "ldexpf" | "log1p" | "log1pf" | "log2f" | "modf"
            | "modff" | "feclearexcept" | "fetestexcept" | "fegetround" | "fesetround"
            | "sincos" | "sincosf" | "_sincos_stret" | "__sincos_stret" | "sincos_stret"
            | "__exp10"
            // libc string / stdio / formatting
            | "atoi" | "atol" | "atoll" | "atof" | "bzero" | "memccpy" | "strcasecmp"
            | "strncasecmp" | "strnlen" | "strpbrk" | "strspn" | "strcspn" | "strsep"
            | "strsignal" | "strerror_r" | "strtof" | "strftime" | "strptime" | "putchar"
            | "fgetc" | "getc" | "ungetc" | "scanf" | "sscanf" | "fscanf" | "vsnprintf"
            | "vfprintf" | "vprintf" | "vsprintf" | "remove" | "uuid_unparse" | "uuid_generate"
            // libc process / fs / signals / misc
            | "alarm" | "pause" | "raise" | "wait" | "wait4" | "waitid" | "execv" | "execvp"
            | "execvpe" | "chmod" | "fchmod" | "chown" | "fchown" | "lchown" | "chroot"
            | "umask" | "link" | "linkat" | "unlinkat" | "openat" | "fstatat" | "statfs"
            | "fstatfs" | "fsync" | "fdatasync" | "futimens" | "utimensat" | "isatty"
            | "openpty" | "ttyname" | "ttyname_r" | "ptsname" | "grantpt" | "unlockpt"
            | "posix_openpt" | "tcgetattr" | "tcsetattr" | "tcdrain" | "tcflush" | "cfmakeraw"
            | "getentropy" | "getrandom" | "getpagesize" | "getrlimit" | "setrlimit"
            | "getrusage" | "getpriority" | "setpriority" | "getsid" | "setsid" | "setpgid"
            | "getpgid" | "setgid" | "setuid" | "setgroups" | "getgroups" | "getpeername"
            | "getsockname" | "shutdown" | "gethostuuid" | "gethostname" | "sethostname"
            | "gai_strerror" | "getnameinfo" | "sigprocmask" | "sigpending" | "sigsuspend"
            | "sigwait" | "longjmp" | "setjmp" | "_setjmp" | "_longjmp" | "siglongjmp"
            | "sigsetjmp" | "gmtime_r" | "localtime_r" | "mktime" | "timegm" | "asctime_r"
            | "ctime_r" | "sched_yield" | "shm_open" | "shm_unlink" | "madvise"
            | "posix_madvise" | "msync" | "mlock" | "munlock" | "backtrace"
            | "backtrace_symbols" | "dladdr" | "dlinfo" | "getpwnam_r" | "getgrnam_r"
            | "getgrgid_r" | "getpwnam" | "uname" | "putenv"
            // Apple-specific copyfile / clonefile / malloc-zone / mach / objc-glue
            | "copyfile" | "fcopyfile" | "copyfile_state_alloc" | "copyfile_state_free"
            | "copyfile_state_get" | "copyfile_state_set" | "clonefile" | "fclonefileat"
            | "clonefileat" | "malloc_default_zone" | "malloc_zone_statistics"
            | "malloc_zone_malloc" | "malloc_size" | "malloc_good_size"
            | "memset_pattern16" | "memset_pattern8" | "memset_pattern4"
            | "sys_icache_invalidate" | "sys_dcache_flush" | "proc_pid_rusage"
            | "task_get_exception_ports" | "task_set_exception_ports"
            // low-level C runtime / EH glue resolved by libSystem / compiler-rt
            | "__assert_rtn" | "_assert_rtn" | "__chkstk_darwin" | "_chkstk_darwin"
            | "__register_frame" | "_register_frame" | "__deregister_frame"
            | "_deregister_frame" | "__dso_handle" | "_dso_handle" | "__memcpy_chk"
            | "_memcpy_chk" | "__memmove_chk" | "__memset_chk" | "__strcpy_chk"
            | "__strcat_chk" | "__snprintf_chk" | "__sprintf_chk" | "__vsnprintf_chk"
            | "__gxx_personality_v0" | "_gxx_personality_v0" | "__DefaultRuneLocale"
            | "_DefaultRuneLocale" | "__Exit" | "_Exit"
    ) {
        return true;
    }

    false
}

fn is_known_system_name(name: &str) -> bool {
    if name.starts_with("_Z") || name.starts_with("__Z") {
        return true;
    }
    matches!(
        name,
        "malloc"
            | "_GLOBAL_OFFSET_TABLE_"
            | "GLOBAL_OFFSET_TABLE_"
            | "calloc"
            | "realloc"
            | "free"
            | "posix_memalign"
            | "aligned_alloc"
            | "memcpy"
            | "memmove"
            | "memset"
            | "memcmp"
            | "memchr"
            | "strlen"
            | "strcmp"
            | "strncmp"
            | "strcpy"
            | "strncpy"
            | "strcat"
            | "strdup"
            | "strerror"
            | "strstr"
            | "strchr"
            | "strrchr"
            | "strtol"
            | "strtoul"
            | "strtod"
            | "strtoll"
            | "strtoull"
            | "printf"
            | "fprintf"
            | "sprintf"
            | "snprintf"
            | "puts"
            | "fputs"
            | "fputc"
            | "fwrite"
            | "fread"
            | "fgets"
            | "fopen"
            | "fclose"
            | "popen"
            | "pclose"
            | "fflush"
            | "fseek"
            | "ftell"
            | "rewind"
            | "feof"
            | "ferror"
            | "fileno"
            | "fdopen"
            | "freopen"
            | "getline"
            | "getdelim"
            | "stdin"
            | "stdout"
            | "stderr"
            | "sqrt"
            | "sqrtf"
            | "sin"
            | "cos"
            | "tan"
            | "asin"
            | "acos"
            | "atan"
            | "atan2"
            | "exp"
            | "expf"
            | "log"
            | "logf"
            | "log2"
            | "log10"
            | "pow"
            | "powf"
            | "fabs"
            | "fabsf"
            | "ceil"
            | "ceilf"
            | "floor"
            | "floorf"
            | "round"
            | "roundf"
            | "fmod"
            | "fmodf"
            | "fmin"
            | "fmax"
            | "copysign"
            | "nan"
            | "isnan"
            | "isinf"
            | "trunc"
            | "truncf"
            | "exit"
            | "_exit"
            | "abort"
            | "atexit"
            | "getenv"
            | "setenv"
            | "unsetenv"
            | "system"
            | "fork"
            | "execve"
            | "execvp"
            | "waitpid"
            | "kill"
            | "getpid"
            | "getppid"
            | "signal"
            | "sigaction"
            | "sigemptyset"
            | "sigfillset"
            | "sigaddset"
            | "pthread_create"
            | "pthread_join"
            | "pthread_detach"
            | "pthread_atfork"
            | "pthread_self"
            | "pthread_mutex_init"
            | "pthread_mutex_lock"
            | "pthread_mutex_unlock"
            | "pthread_mutex_destroy"
            | "pthread_rwlock_init"
            | "pthread_rwlock_destroy"
            | "pthread_rwlock_rdlock"
            | "pthread_rwlock_wrlock"
            | "pthread_rwlock_unlock"
            | "pthread_cond_init"
            | "pthread_cond_wait"
            | "pthread_cond_signal"
            | "pthread_cond_broadcast"
            | "pthread_cond_destroy"
            | "dlopen"
            | "dlclose"
            | "dlsym"
            | "dlerror"
            | "open"
            | "close"
            | "read"
            | "write"
            | "lseek"
            | "stat"
            | "fstat"
            | "lstat"
            | "mkdir"
            | "rmdir"
            | "unlink"
            | "rename"
            | "getcwd"
            | "chdir"
            | "access"
            | "realpath"
            | "readlink"
            | "symlink"
            | "opendir"
            | "readdir"
            | "readdir_r"
            | "closedir"
            | "dirfd"
            | "fdopendir"
            | "scandir"
            | "getdirentries64"
            | "socket"
            | "bind"
            | "listen"
            | "accept"
            | "connect"
            | "send"
            | "recv"
            | "sendto"
            | "recvfrom"
            | "setsockopt"
            | "getsockopt"
            | "getaddrinfo"
            | "freeaddrinfo"
            | "inet_ntop"
            | "inet_pton"
            | "htons"
            | "ntohs"
            | "htonl"
            | "time"
            | "clock"
            | "clock_gettime"
            | "gettimeofday"
            | "nanosleep"
            | "usleep"
            | "sleep"
            | "qsort"
            | "bsearch"
            | "abs"
            | "labs"
            | "rand"
            | "srand"
            | "isdigit"
            | "isalpha"
            | "isspace"
            | "tolower"
            | "toupper"
            | "mmap"
            | "munmap"
            | "mprotect"
            | "sysconf"
            | "pipe"
            | "dup"
            | "dup2"
            | "fcntl"
            | "ioctl"
            | "select"
            | "poll"
            | "gnu_get_libc_version"
            | "confstr"
            | "getauxval"
            | "dl_iterate_phdr"
            | "__libc_start_main"
            | "__cxa_atexit"
            | "__cxa_finalize"
            | "__cxa_thread_atexit_impl"
            | "__errno_location"
            | "__stack_chk_fail"
            | "__stack_chk_guard"
            | "posix_spawn"
            | "posix_spawnattr_init"
            | "posix_spawnattr_setflags"
            | "posix_spawnattr_setsigdefault"
            | "posix_spawnattr_setsigmask"
            | "posix_spawnattr_setpgroup"
            | "posix_spawnattr_destroy"
            | "posix_spawn_file_actions_init"
            | "posix_spawn_file_actions_adddup2"
            | "posix_spawn_file_actions_addopen"
            | "posix_spawn_file_actions_addclose"
            | "posix_spawn_file_actions_destroy"
            | "posix_spawnp"
            | "setlocale"
            | "nl_langinfo"
            | "getpwuid_r"
            | "getuid"
            | "geteuid"
            | "prctl"
            | "sched_getaffinity"
            | "getrandom"
            | "syscall"
            | "__tls_get_addr"
            | "_Unwind_Backtrace"
            | "_Unwind_FindEnclosingFunction"
            | "_Unwind_GetCFA"
            | "_Unwind_GetDataRelBase"
            | "_Unwind_GetIP"
            | "_Unwind_GetIPInfo"
            | "_Unwind_GetLanguageSpecificData"
            | "_Unwind_GetRegionStart"
            | "_Unwind_GetTextRelBase"
            | "_Unwind_Resume"
            | "_Unwind_SetGR"
            | "_Unwind_SetIP"
            | "cfgetispeed"
            | "cfgetospeed"
            | "cfsetispeed"
            | "cfsetospeed"
            | "cfsetspeed"
            | "epoll_create1"
            | "epoll_ctl"
            | "epoll_wait"
            | "eventfd"
            | "futex"
            | "madvise"
            | "mremap"
            | "mincore"
    )
}
