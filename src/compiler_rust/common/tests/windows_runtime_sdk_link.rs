//! Real SDK import closure regression; run in an initialized x64 MSVC SDK environment.
//! No imported API is called: the executable verifies sixteen resolved addresses.
#![cfg(all(windows, target_arch = "x86_64", target_env = "msvc"))]

use simple_common::platform::link_config::PlatformLinkConfig;
use simple_common::target::Target;
use std::{fs, path::Path, process::Command, time::{SystemTime, UNIX_EPOCH}};

const REQUIRED: [&str; 4] = ["pdh", "powrprof", "netapi32", "psapi"];
const SOURCE: &str = include_str!("fixtures/windows_runtime_sdk_imports.c");

fn diagnostic(output: &std::process::Output) -> String {
    format!("status={}\n{}\n{}", output.status,
        String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr))
}

#[test]
fn windows_runtime_sdk_imports_link_and_execute_with_actual_policy() {
    let target = Target::parse("x86_64-pc-windows-msvc").unwrap();
    let policy = PlatformLinkConfig::for_target(&target);
    let compiler = std::env::var_os("SIMPLE_SDK_CLANG_CL")
        .unwrap_or_else(|| "clang-cl.exe".into());
    let stamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let root = std::env::temp_dir().join(format!("simple-sdk-imports-{}-{stamp}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let source = root.join("imports.c");
    let object = root.join("imports.obj");
    fs::write(&source, SOURCE).unwrap();
    let compiled = Command::new(&compiler).args(["/nologo", "/c", "/Od", "/MD"])
        .arg(&source).arg(format!("/Fo{}", object.display())).output()
        .expect("clang-cl is required; initialize the actual MSVC SDK environment");
    assert!(compiled.status.success(), "C fixture compilation failed: {}", diagnostic(&compiled));

    // An optional retained old-source policy emitter supplies the actual historical
    // library list. Otherwise the negative is the actual current policy minus the
    // four provider families; it is not claimed to be a historical binary receipt.
    let negative: Vec<String> = match std::env::var_os("SIMPLE_SDK_LEGACY_LIBRARIES") {
        Some(path) => fs::read_to_string(path).unwrap().lines().map(str::to_owned).collect(),
        None => policy.libraries.iter().filter(|name| !REQUIRED.contains(name))
            .map(|name| (*name).to_owned()).collect(),
    };
    assert!(!negative.is_empty());
    for name in &negative {
        assert!(name.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_'));
        assert!(!REQUIRED.contains(&name.as_str()), "negative policy already supplies {name}");
    }
    let link = |output: &Path, libraries: &[String]| {
        Command::new(&compiler).arg("/nologo").arg(&object)
            .arg(format!("/Fe{}", output.display())).arg("/link")
            .args(libraries.iter().map(|name| format!("{name}.lib")))
            .output().expect("clang-cl link invocation")
    };
    let missing = link(&root.join("missing.exe"), &negative);
    assert!(!missing.status.success(), "missing SDK provider policy unexpectedly linked");
    let errors = diagnostic(&missing);
    for symbol in ["PdhOpenQueryA", "CallNtPowerInformation", "GetModuleFileNameExW", "NetUserEnum"] {
        assert!(errors.contains(symbol), "negative link did not diagnose {symbol}: {errors}");
    }
    let executable = root.join("resolved.exe");
    let libraries: Vec<String> = policy.libraries.iter().map(|name| (*name).to_owned()).collect();
    let linked = link(&executable, &libraries);
    assert!(linked.status.success(), "actual policy failed SDK closure: {}", diagnostic(&linked));
    let run = Command::new(&executable).output().expect("execute linked SDK fixture");
    assert!(run.status.success(), "SDK address fixture failed: {}", diagnostic(&run));
    assert_eq!(String::from_utf8_lossy(&run.stdout).replace("\r\n", "\n"), "sdk-imports=16\n");
    assert!(run.stderr.is_empty(), "unexpected fixture stderr");
    println!("SDK closure: old/missing policy FAIL, actual current policy link+run PASS; evidence={}", root.display());
    // Keep successful and failed link artifacts for the bounded outer receipt.
}
