//! Detect which LLVM targets the linked LLVM provides, so `codegen::llvm_jit`
//! only references per-target initializer symbols that exist at link time.
//! Emits `llvm_has_arm` / `llvm_has_riscv` / `llvm_has_aarch64` / `llvm_has_x86`.
//! llvm-config lookup mirrors vendor/aya-llvm-sys/build.rs: if
//! LLVM_SYS_231_PREFIX is set only `$PREFIX/bin` is searched, otherwise PATH
//! with major >= 23. If none is found, assume every target is present.
use std::path::PathBuf;
use std::process::Command;

const NAMES: [&str; 6] = [
    "llvm-config",
    "llvm-config-23",
    "llvm-config23",
    "llvm23-config",
    "llvm-config-23.1",
    "llvm-config231",
];

fn run(cmd: &PathBuf, arg: &str) -> Option<String> {
    let out = Command::new(cmd).arg(arg).output().ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

fn is_23(cmd: &PathBuf) -> bool {
    run(cmd, "--version")
        .and_then(|v| v.trim().split('.').next().and_then(|m| m.parse::<u32>().ok()))
        .map_or(false, |m| m >= 23)
}

fn targets_built() -> Option<String> {
    let prefix = std::env::var_os("LLVM_SYS_231_PREFIX").map(|p| PathBuf::from(p).join("bin"));
    for n in NAMES {
        let cmd = match &prefix {
            Some(p) => p.join(n),
            None => PathBuf::from(n),
        };
        if is_23(&cmd) {
            if let Some(t) = run(&cmd, "--targets-built") {
                return Some(t);
            }
        }
    }
    None
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=LLVM_SYS_231_PREFIX");
    if let Some(p) = std::env::var_os("LLVM_SYS_231_PREFIX") {
        println!("cargo:rerun-if-changed={}", PathBuf::from(p).display());
    }
    println!("cargo::rustc-check-cfg=cfg(llvm_has_arm)");
    println!("cargo::rustc-check-cfg=cfg(llvm_has_riscv)");
    println!("cargo::rustc-check-cfg=cfg(llvm_has_aarch64)");
    println!("cargo::rustc-check-cfg=cfg(llvm_has_x86)");
    if std::env::var_os("CARGO_FEATURE_LLVM").is_none() {
        return;
    }
    let built = targets_built();
    let has = |name: &str| match &built {
        Some(s) => s.split_whitespace().any(|t| t == name),
        None => true,
    };
    for (t, cfg) in [("ARM", "arm"), ("RISCV", "riscv"), ("AArch64", "aarch64"), ("X86", "x86")] {
        if has(t) {
            println!("cargo:rustc-cfg=llvm_has_{}", cfg);
        }
    }
}
