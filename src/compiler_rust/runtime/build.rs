use std::env;
use std::fs;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=../common/src/runtime_symbols.rs");
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=../../runtime/runtime_math.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_memory.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_time.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_ctype.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_random.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_hash.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_value.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_equality.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_config.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_crypto.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_contracts.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_env.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_base64.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_format.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_error.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_regex_stub.c");
    println!("cargo:rerun-if-changed=../../runtime/runtime_value.h");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_DRIVER_HOOKS");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_RUNTIME_SYMBOL_TABLE");

    compile_c_runtime_sources();

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let source = manifest_dir.join("../common/src/runtime_symbols.rs");
    let content = fs::read_to_string(&source).expect("read runtime_symbols.rs");
    let runtime_src = manifest_dir.join("src");
    let runtime_symbol_table = env::var_os("CARGO_FEATURE_RUNTIME_SYMBOL_TABLE").is_some();

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

    generated.push_str("mod exported_symbols {\n");
    generated.push_str("    unsafe extern \"C\" {\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, symbol) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                // Under driver-hooks, native_all owns the real C symbol; skip the unconditional
                // link-name reference here to avoid an unresolved-symbol error in simple-driver.
                continue;
            }
            generated.push_str(&format!("        pub fn {symbol}();\n"));
        }
    }
    generated.push_str("    }\n");
    generated.push_str("}\n\n");
    generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, symbol) {
            if driver_hooks && DRIVER_HOOK_SYMBOLS.contains(&symbol.as_str()) {
                // Omit from the static table; native_all registers the real symbol separately
                // when it links in (it owns the #[no_mangle] definition).
                continue;
            }
            generated.push_str(&format!(
                "    RuntimeSymbolEntry::new(\"{symbol}\", exported_symbols::{symbol} as *const u8),\n"
            ));
        }
    }
    generated.push_str("];\n");

    fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
}

fn compile_c_runtime_sources() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let runtime_c_dir = manifest_dir.join("../../runtime");
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));

    let c_sources = ["runtime_math.c", "runtime_memory.c", "runtime_time.c", "runtime_ctype.c", "runtime_random.c", "runtime_hash.c", "runtime_value.c", "runtime_equality.c", "runtime_config.c", "runtime_crypto.c", "runtime_contracts.c", "runtime_env.c", "runtime_base64.c", "runtime_format.c", "runtime_error.c", "runtime_regex_stub.c"];
    let mut objects = Vec::new();

    for source in &c_sources {
        let src_path = runtime_c_dir.join(source);
        if !src_path.exists() {
            continue;
        }
        let obj_name = source.replace(".c", ".o");
        let obj_path = out_dir.join(&obj_name);
        let status = std::process::Command::new("cc")
            .arg("-c")
            .arg("-O2")
            .arg("-fPIC")
            .arg("-std=gnu11")
            .arg(&src_path)
            .arg("-o")
            .arg(&obj_path)
            .status();
        if let Ok(s) = status {
            if s.success() {
                objects.push(obj_path);
            }
        }
    }

    if !objects.is_empty() {
        let archive = out_dir.join("libruntime_sffi_c.a");
        let mut cmd = std::process::Command::new("ar");
        cmd.arg("rcs").arg(&archive);
        for obj in &objects {
            cmd.arg(obj);
        }
        if let Ok(s) = cmd.status() {
            if s.success() {
                println!("cargo:rustc-link-search=native={}", out_dir.display());
                println!("cargo:rustc-link-lib=static=runtime_sffi_c");
                println!("cargo:rustc-link-lib=dylib=m");
            }
        }
    }
}

fn runtime_defines_symbol(root: &Path, symbol: &str) -> bool {
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
            if let Ok(file) = fs::read_to_string(&entry_path) {
                if file.contains(&needle) {
                    return true;
                }
            }
        }
    }

    false
}
