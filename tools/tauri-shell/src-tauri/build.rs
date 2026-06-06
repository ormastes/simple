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

// Emits the include for the UI source bundle tarball. Precedence:
//   1. SIMPLE_MOBILE_UI_BUNDLE env var (explicit path)
//   2. the default `ui_bundle.tar.gz` next to this build.rs, if it exists
//   3. None (keeps the crate compiling when no bundle is present)
fn ui_bundle_include_line(const_name: &str) -> String {
    println!("cargo:rerun-if-env-changed=SIMPLE_MOBILE_UI_BUNDLE");

    let bundle_path = match env::var("SIMPLE_MOBILE_UI_BUNDLE") {
        Ok(path) if !path.trim().is_empty() => Some(PathBuf::from(path.trim())),
        _ => {
            let default_path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap_or_default())
                .join("ui_bundle.tar.gz");
            println!("cargo:rerun-if-changed={}", default_path.display());
            if default_path.exists() {
                Some(default_path)
            } else {
                None
            }
        }
    };

    match bundle_path {
        Some(path) => {
            println!("cargo:rerun-if-changed={}", path.display());
            format!(
                "pub const {}: Option<&'static [u8]> = Some(include_bytes!(r#\"{}\"#));\n",
                const_name,
                path.display()
            )
        }
        None => format!("pub const {}: Option<&'static [u8]> = None;\n", const_name),
    }
}

fn write_mobile_runtime_assets(out_dir: &Path) {
    let generated = [
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_AARCH64", "ANDROID_RUNTIME_AARCH64"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_X86_64", "ANDROID_RUNTIME_X86_64"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_ARMV7", "ANDROID_RUNTIME_ARMV7"),
        runtime_include_line("SIMPLE_ANDROID_RUNTIME_I686", "ANDROID_RUNTIME_I686"),
        runtime_include_line("SIMPLE_IOS_RUNTIME_AARCH64", "IOS_RUNTIME_AARCH64"),
        runtime_include_line("SIMPLE_IOS_RUNTIME_AARCH64_SIM", "IOS_RUNTIME_AARCH64_SIM"),
        runtime_include_line("SIMPLE_IOS_RUNTIME_X86_64_SIM", "IOS_RUNTIME_X86_64_SIM"),
        runtime_include_line("SIMPLE_MOBILE_ENTRY_SOURCE", "MOBILE_ENTRY_SOURCE"),
        ui_bundle_include_line("MOBILE_UI_BUNDLE"),
    ]
    .join("");

    let output_path = out_dir.join("mobile_runtime_assets.rs");
    fs::write(output_path, generated).expect("failed to write mobile runtime asset map");
}

fn copy_android_runtime_to_jni_libs(var: &str, abi: &str) {
    println!("cargo:rerun-if-env-changed={}", var);
    let Ok(path) = env::var(var) else {
        return;
    };
    if path.trim().is_empty() {
        return;
    }

    let runtime_path = PathBuf::from(path.trim());
    println!("cargo:rerun-if-changed={}", runtime_path.display());
    let target_dir = PathBuf::from("gen")
        .join("android")
        .join("app")
        .join("src")
        .join("main")
        .join("jniLibs")
        .join(abi);
    fs::create_dir_all(&target_dir).expect("failed to create Android jniLibs runtime dir");
    fs::copy(
        &runtime_path,
        target_dir.join("libsimple_mobile_runtime_exec.so"),
    )
    .expect("failed to copy Android Simple runtime into jniLibs");
}

fn copy_android_runtimes_to_jni_libs() {
    copy_android_runtime_to_jni_libs("SIMPLE_ANDROID_RUNTIME_AARCH64", "arm64-v8a");
    copy_android_runtime_to_jni_libs("SIMPLE_ANDROID_RUNTIME_X86_64", "x86_64");
    copy_android_runtime_to_jni_libs("SIMPLE_ANDROID_RUNTIME_ARMV7", "armeabi-v7a");
    copy_android_runtime_to_jni_libs("SIMPLE_ANDROID_RUNTIME_I686", "x86");
}

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR missing"));
    write_mobile_runtime_assets(&out_dir);
    copy_android_runtimes_to_jni_libs();
    tauri_build::build();
}
