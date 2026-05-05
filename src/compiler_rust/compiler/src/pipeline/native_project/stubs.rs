//! Stub object generation for unresolved symbols during linking.

use std::path::{Path, PathBuf};

use super::{effective_target, ModuleImports};
use super::tools::{
    find_c_compiler, find_native_all_library, find_runtime_library, is_compiler_rt_builtin_symbol, is_system_symbol,
};

fn is_linker_provided_symbol(sym: &str, defined: &std::collections::HashSet<String>) -> bool {
    matches!(
        sym,
        "_sbss"
            | "_ebss"
            | "__bss_start"
            | "__bss_end"
            | "_stack_top"
            | "_stack_bottom"
            | "_kernel_start"
            | "_kernel_end"
            | "__heap_start"
            | "__heap_end"
            | "__global_pointer$"
    ) || (sym == "spl_start"
        && defined.iter().any(|defined_sym| {
            defined_sym == "spl_start" || defined_sym.ends_with("__spl_start") || defined_sym.ends_with("___start")
        }))
}

fn has_equivalent_defined_symbol(sym: &str, defined: &std::collections::HashSet<String>) -> bool {
    if defined.contains(sym) {
        return true;
    }
    if sym.contains("_dot_") {
        return defined.contains(&sym.replace("_dot_", "."));
    }
    if sym.contains('.') {
        return defined.contains(&sym.replace('.', "_dot_"));
    }
    false
}

fn is_optional_weak_hook_symbol(sym: &str) -> bool {
    matches!(
        sym,
        "spl_main"
            | "rt_set_args"
            | "__simple_runtime_init"
            | "__simple_runtime_shutdown"
            | "__simple_call_module_inits"
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FreestandingUnresolvedMode {
    DeferToLinker,
    StrictPrecheck,
    EmitStubs,
}

fn freestanding_unresolved_mode() -> FreestandingUnresolvedMode {
    if std::env::var("SIMPLE_ALLOW_FREESTANDING_STUBS").as_deref() == Ok("1") {
        FreestandingUnresolvedMode::EmitStubs
    } else if std::env::var("SIMPLE_STRICT_FREESTANDING_PRECHECK").as_deref() == Ok("1") {
        FreestandingUnresolvedMode::StrictPrecheck
    } else {
        FreestandingUnresolvedMode::DeferToLinker
    }
}

/// Generate a legacy stub object file for a FREESTANDING (cross) target.
///
/// Unlike `generate_stub_object`, this does not emit asm using host instructions
/// and does not scan host system libraries. It discovers unresolved symbols across
/// the provided `object_paths` (and any boot objects), filters out symbols defined
/// elsewhere in that same object set. By default this now defers unresolved
/// enforcement to the real linker, which can apply section GC and report only
/// live failures. Set `SIMPLE_STRICT_FREESTANDING_PRECHECK=1` to restore the old
/// eager-failure mode, or `SIMPLE_ALLOW_FREESTANDING_STUBS=1` to emit weak
/// legacy stubs while debugging incomplete ports.
pub(crate) fn generate_stub_object_freestanding(
    temp_dir: &Path,
    object_paths: &[PathBuf],
    boot_objects: &[PathBuf],
    triple: &str,
    march: &str,
    mabi: &str,
) -> Result<Option<PathBuf>, String> {
    use std::collections::{BTreeSet, HashSet};

    fn scan_nm_defined_undefined(path: &Path) -> Option<(HashSet<String>, BTreeSet<String>)> {
        let output = std::process::Command::new("nm")
            .arg("-g")
            .arg("-p")
            .arg(path)
            .output()
            .ok()?;
        if !output.status.success() {
            return None;
        }
        let mut defined = HashSet::new();
        let mut undefined = BTreeSet::new();
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert((*name).to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert((*name).to_string());
                }
                _ => {}
            }
        }
        Some((defined, undefined))
    }

    let mut defined: HashSet<String> = HashSet::new();
    let mut undefined: BTreeSet<String> = BTreeSet::new();

    // Scan both Simple object_paths AND any boot_objects (boot .c/.s may define
    // or reference symbols that must not be stubbed over).
    let scan_paths: Vec<PathBuf> = object_paths.iter().chain(boot_objects.iter()).cloned().collect();
    let worker_count = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    if worker_count <= 1 || scan_paths.len() < 16 {
        for path in &scan_paths {
            if let Some((local_defined, local_undefined)) = scan_nm_defined_undefined(path) {
                defined.extend(local_defined);
                undefined.extend(local_undefined);
            }
        }
    } else {
        let chunk_size = scan_paths.len().div_ceil(worker_count);
        let mut handles = Vec::new();
        for chunk in scan_paths.chunks(chunk_size.max(1)) {
            let chunk_paths = chunk.to_vec();
            handles.push(std::thread::spawn(move || {
                let mut local_defined = HashSet::new();
                let mut local_undefined = BTreeSet::new();
                for path in &chunk_paths {
                    if let Some((defined, undefined)) = scan_nm_defined_undefined(path) {
                        local_defined.extend(defined);
                        local_undefined.extend(undefined);
                    }
                }
                (local_defined, local_undefined)
            }));
        }
        for handle in handles {
            if let Ok((local_defined, local_undefined)) = handle.join() {
                defined.extend(local_defined);
                undefined.extend(local_undefined);
            }
        }
    }

    // Only stub symbols that are genuinely unresolved in the link set.
    // Exclude obvious system/dyld/C++ runtime mangled names.
    let needs_stub: Vec<String> = undefined
        .into_iter()
        .filter(|s| !has_equivalent_defined_symbol(s, &defined))
        .filter(|s| !s.is_empty())
        .filter(|s| {
            s.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.')
        })
        .filter(|s| !s.starts_with("_dyld_"))
        .filter(|s| !s.starts_with("_ZSt") && !s.starts_with("_ZNSt"))
        .filter(|s| !is_system_symbol(s))
        .filter(|s| !is_compiler_rt_builtin_symbol(s))
        .filter(|s| !is_linker_provided_symbol(s, &defined))
        .filter(|s| s != "main" && s != "_main")
        .collect();

    let mut compat_symbols = BTreeSet::new();
    let mut unresolved = Vec::new();
    for sym in needs_stub {
        match sym.as_str() {
            "i64.max" | "i64.min" | "str.repeat" | "bytes_to_u16_le" | "bytes_to_u16_be" | "bytes_to_u32_le"
            | "bytes_to_u32_be" | "rt_str_hash" | "rt_range" | "rt_value_bool" | "rt_unwrap_or_self" | "rt_is_none"
            | "rt_is_some" => {
                compat_symbols.insert(sym);
            }
            _ => unresolved.push(sym),
        }
    }

    eprintln!(
        "Freestanding unresolved symbol check: {} unexpected symbol(s)",
        unresolved.len() + compat_symbols.len()
    );
    if std::env::var("SIMPLE_TRACE_STUBS").is_ok() {
        for s in unresolved.iter().chain(compat_symbols.iter()).take(20) {
            eprintln!("  STUB: {}", s);
        }
        let total = unresolved.len() + compat_symbols.len();
        if total > 20 {
            eprintln!("  ... ({} more)", total - 20);
        }
    }

    if unresolved.is_empty() && compat_symbols.is_empty() {
        return Ok(None);
    }
    let unresolved_mode = freestanding_unresolved_mode();
    match unresolved_mode {
        FreestandingUnresolvedMode::DeferToLinker => {
            eprintln!(
                "Freestanding unresolved precheck deferred to linker: {} candidate symbol(s)",
                unresolved.len()
            );
            if compat_symbols.is_empty() {
                return Ok(None);
            }
        }
        FreestandingUnresolvedMode::StrictPrecheck => {
            if unresolved.is_empty() {
                // Only compatibility aliases remain; emit them below rather than
                // failing the precheck on an empty unresolved set.
            } else {
                return Err(format!(
                    "freestanding link has unexpected unresolved symbol(s): {}",
                    unresolved.join(", ")
                ));
            }
        }
        FreestandingUnresolvedMode::EmitStubs => {}
    }

    let stub_c = temp_dir.join("_stubs_freestanding.c");
    let mut code = String::from("/* Auto-generated freestanding stubs — weak definitions return 0 */\n");
    code.push_str("typedef long long __stub_i64;\n\n");
    if compat_symbols.contains("str.repeat") {
        code.push_str(
            "__stub_i64 lib__common__string_core__str_repeat(__stub_i64, __stub_i64);\n\
             __stub_i64 __stub_compat_str_repeat(__stub_i64 s, __stub_i64 count) __asm__(\"str.repeat\");\n\
             __stub_i64 __stub_compat_str_repeat(__stub_i64 s, __stub_i64 count) {\n\
                 return lib__common__string_core__str_repeat(s, count);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("i64.max") {
        code.push_str(
            "__stub_i64 __stub_compat_i64_max(__stub_i64 a, __stub_i64 b) __asm__(\"i64.max\");\n\
             __stub_i64 __stub_compat_i64_max(__stub_i64 a, __stub_i64 b) {\n\
                 return a >= b ? a : b;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("i64.min") {
        code.push_str(
            "__stub_i64 __stub_compat_i64_min(__stub_i64 a, __stub_i64 b) __asm__(\"i64.min\");\n\
             __stub_i64 __stub_compat_i64_min(__stub_i64 a, __stub_i64 b) {\n\
                 return a <= b ? a : b;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u16_le") {
        code.push_str(
            "unsigned short __stub_compat_bytes_to_u16_le(unsigned char b0, unsigned char b1) __asm__(\"bytes_to_u16_le\");\n\
             unsigned short __stub_compat_bytes_to_u16_le(unsigned char b0, unsigned char b1) {\n\
                 return (unsigned short)(((unsigned short)b1 << 8) | (unsigned short)b0);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u16_be") {
        code.push_str(
            "unsigned short __stub_compat_bytes_to_u16_be(unsigned char b0, unsigned char b1) __asm__(\"bytes_to_u16_be\");\n\
             unsigned short __stub_compat_bytes_to_u16_be(unsigned char b0, unsigned char b1) {\n\
                 return (unsigned short)(((unsigned short)b0 << 8) | (unsigned short)b1);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u32_le") {
        code.push_str(
            "unsigned int __stub_compat_bytes_to_u32_le(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) __asm__(\"bytes_to_u32_le\");\n\
             unsigned int __stub_compat_bytes_to_u32_le(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) {\n\
                 return ((unsigned int)b0) | ((unsigned int)b1 << 8) | ((unsigned int)b2 << 16) | ((unsigned int)b3 << 24);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("bytes_to_u32_be") {
        code.push_str(
            "unsigned int __stub_compat_bytes_to_u32_be(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) __asm__(\"bytes_to_u32_be\");\n\
             unsigned int __stub_compat_bytes_to_u32_be(unsigned char b0, unsigned char b1, unsigned char b2, unsigned char b3) {\n\
                 return ((unsigned int)b3) | ((unsigned int)b2 << 8) | ((unsigned int)b1 << 16) | ((unsigned int)b0 << 24);\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_str_hash") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_str_hash(__stub_i64 s) __asm__(\"rt_str_hash\");\n\
             __stub_i64 __stub_compat_rt_str_hash(__stub_i64 s) {\n\
                 const unsigned long long offset = 14695981039346656037ULL;\n\
                 const unsigned long long prime = 1099511628211ULL;\n\
                 const unsigned char* p = (const unsigned char*)(unsigned long long)s;\n\
                 unsigned long long h = offset;\n\
                 if (!p) {\n\
                     return (__stub_i64)h;\n\
                 }\n\
                 while (*p) {\n\
                     h ^= (unsigned long long)(*p++);\n\
                     h *= prime;\n\
                 }\n\
                 return (__stub_i64)h;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_range") {
        code.push_str(
            "__stub_i64 rt_array_new(__stub_i64 cap);\n\
             signed char rt_array_push(__stub_i64 arr, __stub_i64 val);\n\
             __stub_i64 __stub_compat_rt_range(__stub_i64 start, __stub_i64 end) __asm__(\"rt_range\");\n\
             __stub_i64 __stub_compat_rt_range(__stub_i64 start, __stub_i64 end) {\n\
                 if (end <= start) return rt_array_new(0);\n\
                 __stub_i64 result = rt_array_new(end - start);\n\
                 if (result == 3) return result;\n\
                 for (__stub_i64 value = start; value < end; value++) {\n\
                     (void)rt_array_push(result, value << 3);\n\
                 }\n\
                 return result;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_value_bool") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_value_bool(unsigned char b) __asm__(\"rt_value_bool\");\n\
             __stub_i64 __stub_compat_rt_value_bool(unsigned char b) {\n\
                return b ? 11 : 19;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_unwrap_or_self") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_unwrap_or_self(__stub_i64 val) __asm__(\"rt_unwrap_or_self\");\n\
             __stub_i64 __stub_compat_rt_unwrap_or_self(__stub_i64 val) {\n\
                 if (val == 3) return 3;\n\
                 if ((((unsigned long long)val) & 0x7ULL) != 0x1ULL) return val;\n\
                 __stub_i64* p = (__stub_i64*)((((unsigned long long)val) & ~0x7ULL));\n\
                 if (!p) return val;\n\
                 if (((unsigned int)p[0]) != 7U) return val;\n\
                 return p[2] == 3 ? val : p[2];\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_is_none") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_is_none(__stub_i64 val) __asm__(\"rt_is_none\");\n\
             __stub_i64 __stub_compat_rt_is_none(__stub_i64 val) {\n\
                 if (val == 3) return 1;\n\
                 if ((((unsigned long long)val) & 0x7ULL) != 0x1ULL) return 0;\n\
                 __stub_i64* p = (__stub_i64*)((((unsigned long long)val) & ~0x7ULL));\n\
                 if (!p) return 0;\n\
                 if (((unsigned int)p[0]) != 7U) return 0;\n\
                 return p[2] == 3 ? 1 : 0;\n\
             }\n\n",
        );
    }
    if compat_symbols.contains("rt_is_some") {
        code.push_str(
            "__stub_i64 __stub_compat_rt_is_some(__stub_i64 val) __asm__(\"rt_is_some\");\n\
             __stub_i64 __stub_compat_rt_is_some(__stub_i64 val) {\n\
                 return __stub_compat_rt_is_none(val) ? 0 : 1;\n\
             }\n\n",
        );
    }
    if matches!(unresolved_mode, FreestandingUnresolvedMode::EmitStubs) {
        for (i, sym) in unresolved.iter().enumerate() {
            // Sanitize C identifier for the wrapper name; keep the external symbol
            // name exact via an __asm__ label so the linker sees the mangled form.
            let wrapper = format!("__stub_fs_{}", i);
            code.push_str(&format!(
                "__attribute__((weak)) __stub_i64 {wrap}(void) __asm__(\"{sym}\");\n\
                 __attribute__((weak)) __stub_i64 {wrap}(void) {{ return 0; }}\n\n",
                wrap = wrapper,
                sym = sym
            ));
        }
    }

    std::fs::write(&stub_c, &code).map_err(|e| format!("write freestanding stubs: {e}"))?;

    let stub_o = temp_dir.join("_stubs_freestanding.o");
    let cc = find_c_compiler();
    let compilers: Vec<String> = {
        let mut v = vec![];
        #[cfg(target_os = "macos")]
        for p in [
            "/opt/homebrew/opt/llvm@18/bin/clang",
            "/opt/homebrew/opt/llvm/bin/clang",
            "/usr/local/opt/llvm/bin/clang",
        ] {
            if std::path::Path::new(p).exists() && !v.contains(&p.to_string()) {
                v.push(p.to_string());
            }
        }
        if !v.contains(&cc) {
            v.push(cc.clone());
        }
        v
    };

    let mut last_stderr = String::new();
    for compiler in &compilers {
        let mut cmd = std::process::Command::new(compiler);
        cmd.args(["-c", "-ffreestanding", "-nostdlib", "-fno-pie"])
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .arg(format!("--target={}", triple));
        if triple.contains("x86_64") {
            cmd.arg("-mno-red-zone");
        }
        if !march.is_empty() {
            cmd.arg(march);
        }
        if !mabi.is_empty() {
            cmd.arg(mabi);
        }
        // For RISC-V, medany needed for freestanding.
        if march.contains("rv") {
            cmd.arg("-mcmodel=medany");
        }

        let output = cmd
            .output()
            .map_err(|e| format!("compile freestanding stubs ({compiler}): {e}"))?;
        if output.status.success() {
            return Ok(Some(stub_o));
        }
        last_stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    }
    Err(format!("failed to compile freestanding stubs: {}", last_stderr))
}

/// Generate a stub object file that provides weak definitions for all unresolved symbols.
#[cfg(any(
    target_os = "macos",
    target_os = "freebsd",
    target_os = "linux",
    target_os = "windows"
))]
pub(crate) fn generate_stub_object(
    temp_dir: &std::path::Path,
    object_paths: &[PathBuf],
    main_o: &std::path::Path,
    selected_runtime_lib: Option<&std::path::Path>,
    imports: &ModuleImports,
) -> Result<PathBuf, String> {
    use std::collections::{HashSet, BTreeSet};

    let mut defined = HashSet::new();
    let mut undefined = BTreeSet::new();

    let archive_path = temp_dir.join("libspl_objects.a");
    let scan_paths: Vec<&std::path::Path> = if archive_path.exists() {
        vec![archive_path.as_path(), main_o]
    } else {
        let mut v: Vec<&std::path::Path> = object_paths.iter().map(|p| p.as_path()).collect();
        v.push(main_o);
        v
    };

    for path in &scan_paths {
        let output = std::process::Command::new("nm")
            .arg("-g")
            .arg("-p")
            .arg(path)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    let runtime_lib = selected_runtime_lib
        .map(|p| p.to_path_buf())
        .or_else(|| find_native_all_library().or_else(find_runtime_library));
    if let Some(ref rt_path) = runtime_lib {
        let output = std::process::Command::new("nm")
            .arg("-g")
            .arg("-p")
            .arg(rt_path)
            .output()
            .map_err(|e| format!("nm runtime: {e}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            match parts.as_slice() {
                [sym_type, name] if *sym_type == "U" => {
                    undefined.insert(name.to_string());
                }
                [_addr, sym_type, name] if *sym_type != "U" => {
                    defined.insert(name.to_string());
                }
                _ => {}
            }
        }
    }

    let plat_config = simple_common::platform::link_config::PlatformLinkConfig::for_host();
    for lib_path in &plat_config.system_scan_libs {
        if std::path::Path::new(lib_path).exists() {
            let mut nm_cmd = std::process::Command::new("nm");
            for flag in &plat_config.nm_flags {
                nm_cmd.arg(flag);
            }
            nm_cmd.arg(lib_path);
            if let Ok(output) = nm_cmd.output() {
                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if let [_addr, sym_type, name] = parts.as_slice() {
                        if *sym_type != "U" {
                            let base = name.split("@@").next().unwrap_or(name);
                            defined.insert(base.to_string());
                            if base != *name {
                                defined.insert(name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }

    let needs_stub: Vec<String> = undefined
        .into_iter()
        .filter(|s| !defined.contains(s))
        .filter(|s| !s.starts_with("_dyld_") && *s != "_main" && *s != "main")
        .filter(|s| {
            !s.starts_with("_ZSt") && !s.starts_with("_ZNSt") && !s.starts_with("ZSt") && !s.starts_with("ZNSt")
        })
        .filter(|s| !is_optional_weak_hook_symbol(s))
        .filter(|s| !is_system_symbol(s))
        .filter(|s| !s.starts_with('?') && !s.starts_with("__imp_"))
        .collect();

    let is_bootstrap = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
    let is_freestanding = effective_target().os == simple_common::target::TargetOS::None;
    if !is_bootstrap && !is_freestanding {
        let mut simple_symbols = HashSet::new();
        for (raw, mangled_variants) in imports.all_mangled.iter() {
            simple_symbols.insert(raw.clone());
            for mangled in mangled_variants {
                simple_symbols.insert(mangled.clone());
            }
        }
        let internal_missing: Vec<String> = needs_stub
            .iter()
            .filter(|sym| simple_symbols.contains(*sym))
            .cloned()
            .collect();
        if !internal_missing.is_empty() {
            let preview = internal_missing.iter().take(12).cloned().collect::<Vec<_>>().join(", ");
            eprintln!(
                "Warning: {} internal Simple symbol(s) will be stubbed: {}{}",
                internal_missing.len(),
                preview,
                if internal_missing.len() > 12 { " ..." } else { "" }
            );
        }
    }

    if needs_stub.is_empty() {
        let stub_c = temp_dir.join("_stubs.c");
        std::fs::write(&stub_c, "/* no stubs needed */\n").map_err(|e| format!("write stubs: {e}"))?;
        let stub_o = temp_dir.join("_stubs.o");
        let empty_cc = std::env::var("CC").unwrap_or_else(|_| "clang".to_string());
        let status = std::process::Command::new(&empty_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .status()
            .map_err(|e| format!("compile stubs: {e}"))?;
        if !status.success() {
            return Err("failed to compile empty stubs".to_string());
        }
        return Ok(stub_o);
    }

    eprintln!(
        "Generating {} stub functions for unresolved symbols...",
        needs_stub.len()
    );
    let preview = needs_stub.iter().take(80).cloned().collect::<Vec<_>>().join(", ");
    eprintln!(
        "Unresolved symbol preview: {}{}",
        preview,
        if needs_stub.len() > 80 { " ..." } else { "" }
    );

    let forbidden_enum_ctors: Vec<&str> = needs_stub
        .iter()
        .map(|s| s.as_str())
        .filter(|s| matches!(*s, "Some" | "None" | "Ok" | "Err"))
        .collect();
    if !forbidden_enum_ctors.is_empty() {
        return Err(format!(
            "refusing to weak-stub enum short constructors: {}",
            forbidden_enum_ctors.join(", ")
        ));
    }

    if std::env::var("SIMPLE_TRACE_STUBS").is_ok() {
        for s in &needs_stub {
            eprintln!("  STUB: {}", s);
        }
    }

    #[cfg(target_os = "windows")]
    {
        let mut c_code = String::with_capacity(needs_stub.len() * 120);
        c_code.push_str("/* Auto-generated stubs for bootstrap linking (Windows) */\n");
        c_code.push_str("#include <stdint.h>\n\n");
        for sym in &needs_stub {
            if !plat_config.is_valid_asm_label(sym) {
                continue;
            }
            c_code.push_str(&format!(
                "int64_t __stub_{id}(void) __asm__(\"{sym}\");\n\
                 int64_t __stub_{id}(void) {{ return 3; }}\n\n",
                id = sym.replace('.', "_").replace('$', "_"),
                sym = sym
            ));
        }

        let stub_c = temp_dir.join("_stubs.c");
        std::fs::write(&stub_c, &c_code).map_err(|e| format!("write stubs: {e}"))?;

        let stub_o = temp_dir.join("_stubs.o");
        let stub_cc = std::env::var("CC").unwrap_or_else(|_| "gcc".to_string());
        let output = std::process::Command::new(&stub_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_c)
            .output()
            .map_err(|e| format!("compile stubs ({stub_cc}): {e}"))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("failed to compile stub functions ({}): {}", stub_cc, stderr));
        }

        return Ok(stub_o);
    }

    #[cfg(not(target_os = "windows"))]
    {
        let mut asm_code = String::with_capacity(needs_stub.len() * 100);
        asm_code.push_str("/* Auto-generated stubs for bootstrap linking */\n");

        let host_target = simple_common::target::Target::host();
        let ret_nil = simple_common::platform::asm_helpers::asm_ret_nil(&host_target);
        let jmp_prefix = simple_common::platform::asm_helpers::asm_jmp_instruction(&host_target);

        for sym in &needs_stub {
            if !plat_config.is_valid_asm_label(sym) {
                continue;
            }

            if cfg!(target_os = "macos") && sym.starts_with("___builtin_") {
                let real_fn = format!("_{}", &sym["___builtin_".len()..]);
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &real_fn));
                continue;
            }

            let bare = sym.strip_prefix('_').unwrap_or(sym.as_str());
            let rt_sym = format!("_rt_{}", bare);
            if matches!(
                bare,
                "array_len"
                    | "array_new"
                    | "array_get"
                    | "array_set"
                    | "array_append"
                    | "array_push"
                    | "array_pop"
                    | "array_slice"
                    | "array_contains"
                    | "string_new"
                    | "string_len"
                    | "string_concat"
                    | "string_eq"
                    | "string_slice"
                    | "string_char_at"
                    | "string_data"
                    | "string_split"
                    | "string_replace"
                    | "string_find"
                    | "string_rfind"
                    | "alloc"
                    | "free"
                    | "print_str"
                    | "println_str"
                    | "print_value"
                    | "println_value"
            ) && defined.contains(&rt_sym)
            {
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &rt_sym));
                continue;
            }

            asm_code.push_str(&plat_config.generate_stub_asm(sym, ret_nil));
        }

        let stub_s = temp_dir.join("_stubs.s");
        std::fs::write(&stub_s, &asm_code).map_err(|e| format!("write stubs: {e}"))?;

        let stub_o = temp_dir.join("_stubs.o");
        let asm_cc = std::env::var("CC").unwrap_or_else(|_| "clang".to_string());
        let output = std::process::Command::new(&asm_cc)
            .arg("-c")
            .arg("-ffunction-sections")
            .arg("-fdata-sections")
            .arg("-o")
            .arg(&stub_o)
            .arg(&stub_s)
            .output()
            .map_err(|e| format!("assemble stubs ({asm_cc}): {e}"))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("failed to assemble stub functions ({}): {}", asm_cc, stderr));
        }

        Ok(stub_o)
    }
}
