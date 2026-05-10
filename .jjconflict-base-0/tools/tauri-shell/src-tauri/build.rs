use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn runtime_include_line(var: &str, const_name: &str) -> String {
    println!("cargo:rerun-if-env-changed={}", var);
    match env::var(var) {
        Ok(path) if !path.trim().is_empty() => {
            let runtime_path = PathBuf::from(path.trim());
            println!("cargo:rerun-if-changed={}", runtime_path.display());
            format!(
                "pub const {}: Option<&'static [u8]> = Some(include_bytes!(r#\"{}\"#));\n",
                const_name,
                runtime_path.display()
            )
        }
        _ => format!("pub const {}: Option<&'static [u8]> = None;\n", const_name),
    }
}

fn write_mobile_runtime_assets(out_dir: &Path) {
    let generated = [
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_AARCH64", "ANDROID_RUNTIME_AARCH64"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_X86_64", "ANDROID_RUNTIME_X86_64"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_ARMV7", "ANDROID_RUNTIME_ARMV7"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_I686", "ANDROID_RUNTIME_I686"),
    ]
    .join("");

    let output_path = out_dir.join("mobile_runtime_assets.rs");
    fs::write(output_path, generated).expect("failed to write mobile runtime asset map");
}

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR missing"));
    write_mobile_runtime_assets(&out_dir);
    tauri_build::build();
}
