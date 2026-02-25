use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let src = PathBuf::from("src/io/term/nat/term_native.c");

    let lib_name = if cfg!(target_os = "macos") {
        "libterm_native.dylib"
    } else if cfg!(target_os = "windows") {
        "term_native.dll"
    } else {
        "libterm_native.so"
    };

    let lib_path = out_dir.join(lib_name);

    // Compile the C source into a shared library using the system C compiler.
    let status = Command::new("cc")
        .args([
            "-shared",
            "-fPIC",
            src.to_str().expect("path utf8"),
            "-o",
            lib_path.to_str().expect("path utf8"),
        ])
        .status()
        .expect("failed to run cc");

    if !status.success() {
        panic!("cc failed to build native term library");
    }

    println!("cargo:rustc-env=TERM_NATIVE_LIB={}", lib_path.display());
}
