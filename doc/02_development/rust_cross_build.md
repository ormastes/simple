# Rust SimpleOS Cross-Build

Script: `scripts/build_rust_simpleos_cross.sh`

## Prerequisites

- **Nightly toolchain**: `rustup toolchain install nightly`
- **rust-src component** (for build-std): `rustup component add rust-src --toolchain nightly`
- **LLVM with clang for SimpleOS**: run `scripts/build_llvm_simpleos_cross.sh` first
- **SimpleOS sysroot** with `lib/libsimpleos_c.a` built

## Two Build Paths

| | Path A — Seed cross | Path B — Forked rustc |
|---|---|---|
| **When** | `$RUST_SRC` not set or no built rustc | `$RUST_SRC/.../stage1/bin/rustc` exists |
| **Rustc** | System `+nightly` | `$RUST_SRC` fork |
| **Extra flags** | `-Z build-std=core,alloc,compiler_builtins` | none (std already compiled) |
| **First run** | ~10 min (builds std from source) | <1 min (incremental) |
| **Incremental** | <1 min | <1 min |

## Key Env Vars

```bash
RUST_SRC          # path to forked rust repo  (default: $HOME/rust)
TARGET            # target triple              (default: x86_64-unknown-simpleos)
SIMPLEOS_SYSROOT  # sysroot root              (default: $PWD/build/os/sysroot)
LLVM_BUILD        # LLVM install dir          (default: $PWD/build/os/llvm/cross-x86_64)
RUSTC_STAGE       # fork stage to use         (default: 1)
RUST_BUILD_DRY_RUN=1  # print command, do not run
```

## Target JSON Location

`src/os/toolchain/rust/x86_64-unknown-simpleos.json`

Additional targets: `aarch64-unknown-simpleos.json`, `riscv64gc-unknown-simpleos.json`.

## Troubleshooting

| Symptom | Fix |
|---|---|
| `nightly toolchain not found` | `rustup toolchain install nightly` |
| `can't find crate for 'core'` | `rustup component add rust-src --toolchain nightly` |
| `libsimpleos_c.a not found` | Build the SimpleOS sysroot; set `SIMPLEOS_SYSROOT` |
| Linker errors / missing clang | Run `scripts/build_llvm_simpleos_cross.sh` first |
| Wrong target JSON | Verify `src/os/toolchain/rust/${TARGET}.json` exists |

## Convenience wrapper

For everyday cross-compile use:

    scripts/cargo_simpleos.sh build --release -p hello_rs

This wrapper sets `SDKROOT`, `CARGO_TARGET_X86_64_UNKNOWN_SIMPLEOS_LINKER`,
`CC_x86_64_unknown_simpleos`, `AR_x86_64_unknown_simpleos`, and `RUSTFLAGS`
automatically, and appends `-Z build-std=core,alloc,compiler_builtins`. Honors
`LLVM_BUILD`, `SIMPLEOS_SYSROOT`, `RUST_SRC` env overrides. Set
`CARGO_SIMPLEOS_NO_BUILD_STD=1` to skip build-std (e.g., when pointing at a
forked rustc that already has SimpleOS libstd built-in).
