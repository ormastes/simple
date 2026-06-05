use std::env;
use std::fs;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=../common/src/runtime_symbols.rs");
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=../../runtime/runtime_memory.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_time.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_pool.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_value.h");
    println!("cargo:rerun-if-changed=../../runtime/runtime_db.c");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DRIVER_HOOKS");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_RUNTIME_SYMBOL_TABLE");

    compile_c_runtime_sources();

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let source = manifest_dir.join("../common/src/runtime_symbols.rs");
    let content = fs::read_to_string(&source).expect("read runtime_symbols.rs");
    let runtime_src = manifest_dir.join("src");
    let runtime_c_dir = manifest_dir.join("../../runtime");
    let runtime_symbol_table = env::var_os("CARGO_FEATURE_RUNTIME_SYMBOL_TABLE").is_some();
    let runtime_regex = env::var_os("CARGO_FEATURE_RUNTIME_REGEX").is_some();

    // Symbols provided by simple-native-all (not the runtime stub) when driver-hooks is active.
    // Under driver-hooks, the runtime stub is cfg-gated out; the real C symbol lives in native_all.
    // We still emit the symbol-table entry, but use a #[link_name] alias so that simple-driver
    // (which does NOT link native_all) compiles without an unresolved-symbol error.
    let driver_hooks = env::var_os("CARGO_FEATURE_DRIVER_HOOKS").is_some();
    const DRIVER_HOOK_SYMBOLS: &[&str] = &["rt_cli_run_file"];

    let mut seen = HashSet::new();
    let mut symbols = Vec::new();
    let mut in_list = false;

    for line in content.lines() {
        if line.contains("pub const RUNTIME_SYMBOL_NAMES") {
            in_list = true;
            continue;
        }
        if !in_list {
            continue;
        }
        if line.contains("];") {
            break;
        }
        if let Some(start) = line.find('"') {
            let rest = &line[start + 1..];
            if let Some(end) = rest.find('"') {
                let symbol = rest[..end].to_string();
                if seen.insert(symbol.clone()) {
                    symbols.push(symbol);
                }
            }
        }
    }

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let mut generated = String::new();
    generated.push_str("use simple_runtime_abi::RuntimeSymbolEntry;\n\n");

    if !runtime_symbol_table {
        generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[];\n");
        fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
        return;
    }

    generated.push_str("#[allow(clashing_extern_declarations)]\n");
    generated.push_str("mod exported_symbols {\n");
    generated.push_str("    #[allow(clashing_extern_declarations)]\n");
    generated.push_str("    unsafe extern \"C\" {\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, &runtime_c_dir, symbol, runtime_regex) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                // Under driver-hooks, native_all owns the real C symbol; skip the unconditional
                // link-name reference here to avoid an unresolved-symbol error in simple-driver.
                continue;
            }
            let alias = runtime_symbol_alias(symbol);
            generated.push_str(&format!("        #[link_name = \"{symbol}\"]\n"));
            generated.push_str(&format!("        pub fn {alias}();\n"));
        }
    }
    generated.push_str("    }\n");
    generated.push_str("}\n\n");
    generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, &runtime_c_dir, symbol, runtime_regex) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                // Omit from the static table; native_all registers the real symbol separately
                // when it links in (it owns the #[no_mangle] definition).
                continue;
            }
            let alias = runtime_symbol_alias(symbol);
            generated.push_str(&format!(
                "    RuntimeSymbolEntry::new(\"{symbol}\", exported_symbols::{alias} as *const u8),\n"
            ));
        }
    }
    generated.push_str("];\n");

    fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
}

fn compile_c_runtime_sources() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let runtime_c_dir = manifest_dir.join("../../runtime");
    let c_sources = [
        "runtime_memory.c",
        "runtime_time.c",
        "runtime_db.c",
        "runtime_pool.c",
    ];

    let mut build = cc::Build::new();
    build.opt_level(2).warnings(false);
    if env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default() != "msvc" {
        build.flag_if_supported("-std=gnu11");
    }
    for source in &c_sources {
        let src_path = runtime_c_dir.join(source);
        if src_path.exists() {
            build.file(src_path);
        }
    }
    build.compile("runtime_sffi_c");

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os != "windows" {
        println!("cargo:rustc-link-lib=dylib=m");
    }
    // openpty / forkpty live in libutil on Linux and most BSDs.
    // On macOS they are part of libc itself; on Windows the functions don't exist.
    if matches!(target_os.as_str(), "linux" | "freebsd" | "netbsd" | "openbsd") {
        println!("cargo:rustc-link-lib=dylib=util");
    }
}

fn runtime_defines_symbol(root: &Path, c_root: &Path, symbol: &str, runtime_regex: bool) -> bool {
    let needle = format!("fn {symbol}");
    let mut stack = vec![root.to_path_buf()];

    while let Some(path) = stack.pop() {
        let Ok(entries) = fs::read_dir(&path) else {
            continue;
        };
        for entry in entries.flatten() {
            let entry_path = entry.path();
            if entry.file_type().map(|kind| kind.is_dir()).unwrap_or(false) {
                stack.push(entry_path);
                continue;
            }
            if entry_path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
                continue;
            }
            if !runtime_regex && entry_path.file_name().and_then(|name| name.to_str()) == Some("regex.rs") {
                continue;
            }
            if let Ok(file) = fs::read_to_string(&entry_path) {
                if rust_file_exports_symbol(&file, &needle, symbol) {
                    return true;
                }
            }
        }
    }

    c_runtime_defines_symbol(c_root, symbol)
}

fn c_runtime_defines_symbol(root: &Path, symbol: &str) -> bool {
    const LINKED_C_SOURCES: &[&str] = &[
        "runtime_memory.c",
        "runtime_time.c",
        "runtime_db.c",
        "runtime_pool.c",
    ];
    for source in LINKED_C_SOURCES {
        let path = root.join(source);
        let Ok(file) = fs::read_to_string(path) else {
            continue;
        };
        if c_file_exports_symbol(&file, symbol) {
            return true;
        }
    }
    false
}

fn rust_file_exports_symbol(file: &str, needle: &str, symbol: &str) -> bool {
    let lines: Vec<&str> = file.lines().collect();
    for (idx, line) in lines.iter().enumerate() {
        if line.contains(&format!("#[export_name = \"{symbol}\"]")) {
            return true;
        }
        if !line.contains(needle) {
            continue;
        }
        let start = idx.saturating_sub(4);
        if lines[start..idx].iter().any(|prev| prev.trim() == "#[no_mangle]") {
            return true;
        }
    }
    false
}

fn c_file_exports_symbol(file: &str, symbol: &str) -> bool {
    let needle = format!("{symbol}(");
    file.lines().any(|line| {
        let trimmed = line.trim_start();
        !trimmed.starts_with("static ")
            && !trimmed.starts_with("//")
            && trimmed.contains(&needle)
            && trimmed.ends_with('{')
    })
}

fn runtime_symbol_alias(symbol: &str) -> String {
    format!("__simple_runtime_symbol_{}", symbol.replace('.', "_dot_"))
}
