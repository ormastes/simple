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
        // Windows: try cl.exe (MSVC) first, fall back to gcc (MinGW).
        //
        // The cl.exe attempt used to be a bare `Command::new("cl.exe")`, which
        // only works when the invoking shell already has cl.exe on PATH with
        // INCLUDE/LIB set (i.e. a "Developer Command Prompt", or vcvars64.bat
        // already sourced) — NOT true for an ordinary shell (git-bash, a plain
        // cmd.exe, this crate's own sibling `simple-runtime` build script's
        // separately-and-correctly-configured `cc::Build` environment doesn't
        // carry over to a different build script's process). PROVED
        // 2026-08-09: in a plain git-bash session, `where cl.exe` finds
        // nothing, so the bare Command silently fell through to the gcc
        // fallback — which then ALSO failed silently (RC=1, zero stdout/
        // stderr) because this host's MSYS2 mingw64 `cc1.exe` turned out to
        // be non-functional independent of anything in this repo (`cc1.exe
        // --version` itself returned "command not found", exit 127, despite
        // the file existing on disk at a plausible size). Both fallback links
        // in the chain were broken at once, and the failure carried zero
        // diagnostic text to explain why.
        //
        // Fix: use `cc::Build::get_compiler()`, exactly like every other C
        // source in this workspace's build scripts (see
        // `runtime/build.rs`) — it does MSVC discovery itself (via the `cc`
        // crate's `vswhom`/registry probing, the same mechanism `vcvarsall.bat`
        // uses) and returns a `Tool` whose `to_command()` already carries the
        // resolved INCLUDE/LIB/PATH environment, independent of whatever the
        // invoking shell happens to have set.
        let tool = cc::Build::new().opt_level(2).get_compiler();
        let cl_result = tool
            .to_command()
            .args([
                "/LD",
                "/nologo",
                src.to_str().expect("path utf8"),
                &format!("/Fe:{}", lib_path.to_str().expect("path utf8")),
            ])
            .status();

        match cl_result {
            Ok(s) if s.success() => s,
            _ => {
                // Fall back to MinGW gcc (kept for a non-MSVC Windows
                // toolchain; not relied on as the primary path above).
                Command::new("gcc")
                    .args([
                        "-shared",
                        src.to_str().expect("path utf8"),
                        "-o",
                        lib_path.to_str().expect("path utf8"),
                    ])
                    .status()
                    .expect("failed to run gcc (MinGW) after cl.exe also failed")
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
