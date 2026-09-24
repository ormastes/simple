use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let src = PathBuf::from("src/io/term/nat/term_native.c");
    // Cargo build scripts run for HOST, so cfg!(target_*) would select the
    // host ABI during a Windows cross-target build. These variables describe
    // the crate TARGET and are the only valid Windows ABI authority here.
    let target_os = env::var("CARGO_CFG_TARGET_OS").expect("target OS not set");
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap_or_default();

    let lib_name = if target_os == "macos" {
        "libterm_native.dylib"
    } else if target_os == "windows" {
        "term_native.dll"
    } else {
        "libterm_native.so"
    };

    let lib_path = out_dir.join(lib_name);

    // Compile the C source into a shared library using platform-appropriate flags.
    let status = if target_os == "macos" {
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
    } else if target_os == "windows" {
        // Windows bootstrap is Clang-only. The MSVC lane uses clang-cl and the
        // GNU lane uses target-qualified clang. Both lanes stay on their
        // admitted C driver.
        //
        // The cl.exe attempt used to be a bare `Command::new("cl.exe")`, which
        // only works when the invoking shell already has cl.exe on PATH with
        // INCLUDE/LIB set (i.e. a "Developer Command Prompt", or vcvars64.bat
        // already sourced) — NOT true for an ordinary shell (git-bash, a plain
        // cmd.exe, this crate's own sibling `simple-runtime` build script's
        // separately-and-correctly-configured `cc::Build` environment doesn't
        // carry over to a different build script's process). PROVED
        // 2026-08-09: in a plain git-bash session, `where cl.exe` finds
        // nothing, so the bare Command silently fell through to an ambient
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
        // MSVC emits the intermediate object into the CURRENT DIRECTORY (the
        // crate root, inside src/compiler_rust) unless /Fo is given. That
        // mutates the fingerprinted seed-input tree mid-build, so the
        // --full-bootstrap post-cargo fingerprint check aborts with "Rust
        // inputs changed during full bootstrap". Keep the object in OUT_DIR.
        let tool = cc::Build::new().opt_level(2).get_compiler();
        let compiler_name = tool
            .path()
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("");
        if target_env == "msvc" {
            if compiler_name != "clang-cl" && compiler_name != "clang-cl.exe" {
                panic!("Windows MSVC bootstrap requires clang-cl, got {compiler_name}");
            }
            let obj_path = out_dir.join("term_native.obj");
            tool.to_command()
                .args([
                    "/LD",
                    "/nologo",
                    src.to_str().expect("path utf8"),
                    // clang-cl spells attached output paths as /FePATH and
                    // /FoPATH. A colon would create a literal `:C:` file.
                    &format!("/Fe{}", lib_path.to_str().expect("path utf8")),
                    &format!("/Fo{}", obj_path.to_str().expect("path utf8")),
                ])
                .status()
                .expect("failed to run clang-cl")
        } else if target_env == "gnu" {
            if compiler_name != "clang" && compiler_name != "clang.exe" {
                panic!("Windows GNU bootstrap requires clang, got {compiler_name}");
            }
            tool.to_command()
                .args([
                    "--target=x86_64-w64-windows-gnu",
                    "-shared",
                    src.to_str().expect("path utf8"),
                    "-o",
                    lib_path.to_str().expect("path utf8"),
                ])
                .status()
                .expect("failed to run target-qualified clang")
        } else {
            panic!("unsupported Windows target environment {target_env}")
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
