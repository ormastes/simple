# Rust seed `--features llvm` fails to link when host LLVM lacks ARM/RISCV targets

- **Date:** 2026-11-05
- **Status:** FIXED (2026-11-05)
- **Host:** Linux aarch64 (20 cores), release/1.0.0 at `0ff9a746185`
- **Lane:** `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-seed`
  with the default backend (`llvm`)

## Symptom

```
VERDICT — ABORTED: stage=rust-rust-seed-build exit=101 signal=none reason=rust-rust-seed-build
mold: error: undefined symbol: LLVMInitializeARMTargetInfo
mold: error: undefined symbol: LLVMInitializeARMTargetMC
mold: error: undefined symbol: LLVMInitializeARMAsmParser
mold: error: undefined symbol: LLVMInitializeARMDisassembler
mold: error: undefined symbol: LLVMInitializeRISCVTargetInfo
mold: error: undefined symbol: LLVMInitializeRISCVTargetMC
mold: error: undefined symbol: LLVMInitializeRISCVAsmParser
mold: error: undefined symbol: LLVMInitializeRISCVAsmPrinter
mold: error: undefined symbol: LLVMInitializeRISCVDisassembler
error: could not compile `simple-driver` (bin "simple") due to 1 previous error
```

## Cause

With `backend=llvm` (the default), `bootstrap-from-scratch.sh:3041-3042` builds the
seed with `--features llvm` against the LLVM 23 resolved by `platform-detect.shs`
(`LLVM_SYS_231_PREFIX=/home/yoon/dev/llvm/install`). Both LLVM 23 installs on this
host were built with only `AArch64 X86 NVPTX` (`llvm-config --targets-built`;
`/usr/lib/llvm-23` is the same).

`src/compiler_rust/compiler/src/codegen/llvm_jit.rs:79-83` unconditionally (on every
non-FreeBSD host) calls `Target::initialize_arm` together with `initialize_aarch64`,
and `Target::initialize_riscv`. Those reference the ARM/RISCV initializer symbols,
which the host LLVM does not provide. FreeBSD already has a `cfg` carve-out for the
same class (commit `949e7e224c1`).

The seed's LLVM-target requirement is therefore stricter than the LLVM admission
check (major version only), so admission passes and the link fails.

## Workaround (not a fix)

`--backend=cranelift` builds the seed without the llvm feature (this is what the
2026-10-24 p2shard runs on this host used). `SIMPLE_BOOTSTRAP_RUST_LLVM=0` is the
documented alternative for keeping the llvm backend for pure-Simple stages.

## Fix direction

Either gate the ARM/RISCV initializers on what the linked LLVM actually provides
(inkwell `target-*` features chosen from `llvm-config --targets-built`), or make
LLVM admission check `--targets-built` for every initializer the seed references
and fail with a clear message before Cargo.

## Evidence

`build/bootstrap-opus-0/logs/aarch64-unknown-linux-gnu/rust-seed-build.log`
in `/home/yoon/dev/simple-bootstrap` (not tracked).

## Fix (2026-11-05)

New `src/compiler_rust/compiler/build.rs` runs `llvm-config --targets-built`
(`$LLVM_SYS_<ver>_PREFIX/bin/llvm-config`, then `llvm-config-23`, `llvm-config`)
when the `llvm` feature is on and emits `llvm_has_{arm,riscv,aarch64,x86}`
(+ check-cfg), mirroring aya-llvm-sys lookup (LLVM_SYS_231_PREFIX only, else PATH names, major >= 23); all present if llvm-config is not found (old behaviour).
`codegen/llvm_jit.rs::new_for_target` gates each `initialize_*` on its cfg and
returns `Err("LLVM target X is not available: ...")` instead of linking a missing symbol.

Evidence (host LLVM 23 = AArch64 X86 NVPTX): RED `cargo build --release --bin simple
--features llvm` -> 12x `mold: undefined symbol: LLVMInitializeARM*/RISCV*`, rc=101.
GREEN same command rc=0; `simple --version`, `run hello.spl` prints hello,
`compile hello.spl --native --backend llvm` succeeds (does not exercise the error path); default
(cranelift) build rc=0.

Error path: unit tests `codegen::llvm_jit::target_availability_tests` call
`LlvmJitCompiler::new_for_target` for Riscv64 and Arm. Host (no RISCV/ARM): GREEN,
`cargo test --release -p simple-compiler --features llvm --lib target_availability`
-> 2 passed, asserting `LLVM target RISCV is not available` / `LLVM target ARM ...`.
Before the fix the same call could not link at all.
