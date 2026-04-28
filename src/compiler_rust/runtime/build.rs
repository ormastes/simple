use std::env;
use std::fs;
use std::collections::HashSet;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=../common/src/runtime_symbols.rs");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let source = manifest_dir.join("../common/src/runtime_symbols.rs");
    let content = fs::read_to_string(&source).expect("read runtime_symbols.rs");
    let runtime_src = manifest_dir.join("src");

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
    generated.push_str("mod exported_symbols {\n");
    generated.push_str("    unsafe extern \"C\" {\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, symbol) {
            generated.push_str(&format!("        pub fn {symbol}();\n"));
        }
    }
    generated.push_str("    }\n");
    generated.push_str("}\n\n");
    generated.push_str("pub static RUNTIME_SYMBOL_ENTRIES: &[RuntimeSymbolEntry] = &[\n");
    for symbol in &symbols {
        if runtime_defines_symbol(&runtime_src, symbol) {
            generated.push_str(&format!(
                "    RuntimeSymbolEntry::new(\"{symbol}\", exported_symbols::{symbol} as *const u8),\n"
            ));
        }
    }
    generated.push_str("];\n");

    fs::write(out_dir.join("runtime_symbol_entries.rs"), generated).expect("write runtime symbol entries");
}

fn runtime_defines_symbol(root: &PathBuf, symbol: &str) -> bool {
    let needle = format!("fn {symbol}");
    let mut stack = vec![root.clone()];

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
