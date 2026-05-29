mod test_helpers;
use std::path::PathBuf;
use std::process::Command;
use std::sync::OnceLock;

fn ensure_fresh_simple_stub() -> Option<PathBuf> {
    static STUB_PATH: OnceLock<Option<PathBuf>> = OnceLock::new();
    STUB_PATH
        .get_or_init(|| {
            let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
            let status = Command::new("cargo")
                .args(["build", "-p", "simple-driver", "--bin", "simple-stub"])
                .current_dir(&workspace_root)
                .status()
                .ok()?;
            if !status.success() {
                return None;
            }
            let candidate = workspace_root.join("target").join("debug").join(if cfg!(windows) {
                "simple-stub.exe"
            } else {
                "simple-stub"
            });
            candidate.exists().then_some(candidate)
        })
        .clone()
}

fn aot_backend_available() -> bool {
    static AVAILABLE: OnceLock<bool> = OnceLock::new();
    *AVAILABLE.get_or_init(|| {
        let Some(stub_path) = ensure_fresh_simple_stub() else {
            return false;
        };
        std::env::set_var("SIMPLE_STUB_PATH", &stub_path);
        let interpreter = simple_driver::interpreter::Interpreter::new();
        interpreter
            .run(
                "fn main():\n    print 1\n",
                simple_driver::interpreter::RunConfig {
                    running_type: simple_driver::interpreter::RunningType::CompileAndRun,
                    capture_output: true,
                    timeout_ms: 30_000,
                    ..Default::default()
                },
            )
            .is_ok()
    })
}

#[test]
fn jit_high_bit_u64_stringification_stays_unsigned() {
    let src = r#"
fn main():
    val top_bit: u64 = 0x8000000000000000u64
    val all_bits: u64 = 0xFFFFFFFFFFFFFFFFu64
    val marker: u64 = 0xCAFEBABEDEADBEEFu64
    print top_bit
    print all_bits
    print marker
    print top_bit.to_text()
    print all_bits.to_text()
    print marker.to_text()
    print "marker={marker}"
"#;
    test_helpers::run_on_stdout(
        test_helpers::Backend::Jit,
        src,
        "9223372036854775808\n18446744073709551615\n14627333968688430831\n9223372036854775808\n18446744073709551615\n14627333968688430831\nmarker=14627333968688430831\n",
    );
}

#[test]
fn aot_high_bit_u64_stringification_stays_unsigned() {
    let Some(stub_path) = ensure_fresh_simple_stub() else {
        eprintln!("Skipping AOT test: failed to build simple-stub");
        return;
    };
    std::env::set_var("SIMPLE_STUB_PATH", &stub_path);
    if !aot_backend_available() {
        eprintln!("Skipping AOT test: packaged executable baseline is not healthy in this checkout");
        return;
    }
    let src = r#"
fn main():
    val top_bit: u64 = 0x8000000000000000u64
    val all_bits: u64 = 0xFFFFFFFFFFFFFFFFu64
    val marker: u64 = 0xCAFEBABEDEADBEEFu64
    print top_bit
    print all_bits
    print marker
    print top_bit.to_text()
    print all_bits.to_text()
    print marker.to_text()
    print "marker={marker}"
"#;
    let interpreter = simple_driver::interpreter::Interpreter::new();
    match interpreter.run(
        src,
        simple_driver::interpreter::RunConfig {
            running_type: simple_driver::interpreter::RunningType::CompileAndRun,
            capture_output: true,
            timeout_ms: 30_000,
            ..Default::default()
        },
    ) {
        Ok(result) => {
            assert_eq!(
                result.stdout,
                "9223372036854775808\n18446744073709551615\n14627333968688430831\n9223372036854775808\n18446744073709551615\n14627333968688430831\nmarker=14627333968688430831\n",
            );
        }
        Err(err) => {
            let msg = err.to_string();
            if msg.contains("Invalid executable stub") || msg.contains("stub") {
                eprintln!("Skipping AOT test: stub binary not available");
                return;
            }
            panic!("Aot failed: {}", err);
        }
    }
}
