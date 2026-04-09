//! Stub object generation for unresolved symbols during linking.

use std::path::PathBuf;

use super::{effective_target, ModuleImports};
use super::tools::{
    find_native_all_library, find_runtime_library,
    is_system_symbol,
};

/// Generate a stub object file that provides weak definitions for all unresolved symbols.
#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "linux", target_os = "windows"))]
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
            !s.starts_with("_ZSt")
                && !s.starts_with("_ZNSt")
                && !s.starts_with("ZSt")
                && !s.starts_with("ZNSt")
        })
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

    #[cfg(target_os = "windows")]
    {
        let mut c_code = String::with_capacity(needs_stub.len() * 120);
        c_code.push_str("/* Auto-generated stubs for bootstrap linking (Windows) */\n");
        c_code.push_str("#include <stdint.h>\n\n");
        for sym in &needs_stub {
            if !plat_config.is_valid_asm_label(sym) { continue; }
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
            if !plat_config.is_valid_asm_label(sym) { continue; }

            if cfg!(target_os = "macos") && sym.starts_with("___builtin_") {
                let real_fn = format!("_{}", &sym["___builtin_".len()..]);
                asm_code.push_str(&plat_config.generate_builtin_trampoline_asm(sym, jmp_prefix, &real_fn));
                continue;
            }

            let bare = if sym.starts_with('_') { &sym[1..] } else { sym.as_str() };
            let rt_sym = format!("_rt_{}", bare);
            if matches!(bare,
                "array_len" | "array_new" | "array_get" | "array_set" | "array_append"
                | "array_push" | "array_pop" | "array_slice" | "array_contains"
                | "string_new" | "string_len" | "string_concat" | "string_eq"
                | "string_slice" | "string_char_at" | "string_data"
                | "string_split" | "string_replace" | "string_find" | "string_rfind"
                | "alloc" | "free" | "print_str" | "println_str"
                | "print_value" | "println_value"
            ) && defined.contains(&rt_sym) {
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
