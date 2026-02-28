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

    // Compile the C source into a shared library using platform-appropriate flags.
    let status = if cfg!(target_os = "macos") {
        // macOS: -dynamiclib instead of -shared, -fPIC is default
        Command::new("cc")
            .args([
                "-dynamiclib",
                src.to_str().expect("path utf8"),
                "-o",
                lib_path.to_str().expect("path utf8"),
            ])
            .status()
            .expect("failed to run cc")
    } else if cfg!(target_os = "windows") {
        // Windows: try cl.exe (MSVC) first, fall back to gcc (MinGW)
        let cl_result = Command::new("cl.exe")
            .args([
                "/LD",
                src.to_str().expect("path utf8"),
                &format!("/Fe:{}", lib_path.to_str().expect("path utf8")),
            ])
            .status();

        match cl_result {
            Ok(s) if s.success() => s,
            _ => {
                // Fall back to MinGW gcc
                Command::new("gcc")
                    .args([
                        "-shared",
                        src.to_str().expect("path utf8"),
                        "-o",
                        lib_path.to_str().expect("path utf8"),
                    ])
                    .status()
                    .expect("failed to run gcc (MinGW)")
            }
        }
    } else {
        // Linux, FreeBSD, and other Unix: cc -shared -fPIC
        Command::new("cc")
            .args([
                "-shared",
                "-fPIC",
                src.to_str().expect("path utf8"),
                "-o",
                lib_path.to_str().expect("path utf8"),
            ])
            .status()
            .expect("failed to run cc")
    };

    if !status.success() {
        panic!("C compiler failed to build native term library");
    }

    println!("cargo:rustc-env=TERM_NATIVE_LIB={}", lib_path.display());
}
