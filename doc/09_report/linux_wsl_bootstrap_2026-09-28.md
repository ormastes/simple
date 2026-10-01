# Linux WSL bootstrap checkpoint — 2026-09-28

## Scope and toolchain

- Source base: GitHub main `0bd5c2e39b6ffd995209e655d2a00de7fda53372` plus this branch's LLVM and glibc compatibility patch.
- Host: Ubuntu 22.04 WSL, glibc 2.35, 14 visible CPUs, 31 GiB WSL memory.
- LLVM: apt.llvm.org Jammy `23.1.2` extracted under `~/.local/toolchains/llvm-23.1.2-apt`; `llvm-config --shared-mode` reports `shared` and `libLLVM-23.so` is present. The official LLVM 23.1.1 Linux X64 archive was verified against SHA-256 `832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c`, but its static distribution lacks the shared library required by platform detection.
- Rust: existing `rustc`/Cargo 1.101.0 nightly. `SIMPLE_NO_STUB_FALLBACK=1` and `BOOTSTRAP_STAGE2_TEST_DELEGATE=0` were set.

## Compatibility fixes and focused evidence

- Admit LLVM 23.1.2 only when the build host is Linux or FreeBSD; Windows and macOS remain pinned to 23.1.1. Update the Rust LLVM binding's host check and vendored checksum together. `bootstrap_llvm23_platform_detection_test.shs`: PASS.
- Remove global Linux `-z pack-relative-relocs` from Cargo config. On glibc 2.35 it caused the Rust seed and Cargo build scripts to require unavailable `GLIBC_ABI_DT_RELR`. The Cargo smoke builds, runs, and inspects a binary under the repository config; `bootstrap_linux_glibc_link_compat_test.shs`: PASS. This proves the narrow RELR compatibility property, not compatibility of every linked dependency with glibc 2.35.

## Bootstrap and performance evidence

The full bootstrap selected **9 native jobs** from 14 CPUs after its memory clamp. The Rust seed/runtime rebuild took **430 seconds**. The Stage 2 seed compiler used approximately **8–9 CPU cores** and **0.8–1.1 GiB RSS** while compiling its closure. The Stage 2 build log ran from 12:22:44 to 12:34:03 Asia/Seoul (about **11m 19s**) and reported `compiled=1058 reused=0 failed=2`. A seed `--version` invocation took **0.01 seconds**, max RSS **86,764 KiB**; seed size was **202,705,320 bytes**. There is no same-source baseline for a speedup or slowdown claim. Removing RELR may increase binary size or startup relocation work; measure that against a compatible baseline before claiming a performance result.

## Current blocker

Stage 2 aborted before admission on two source failures:

1. `src/lib/nogc_sync_mut/sffi/dynlib_lifetime_owner_v1.spl`: `hir: Cannot infer field type: struct 'i64' field 'entries'`.
2. `src/lib/nogc_sync_mut/src/math/rendering.spl`: `llvm codegen: semantic: cannot resolve method call to_latex` on a receiver treated as a builtin type.

Both are seed compiler/source issues also seen in the parallel Windows lane; neither is a new Linux toolchain failure. No Stage 2, Stage 3, or Stage 4 admission receipt exists from this run. The preserved logs are `build/bootstrap/windows-linux-20260927/linux/console-current-main-glibc.log` and `build/bootstrap/windows-linux-20260927/linux/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`. After those source fixes land, rerun the cached Stage 2 build before any Stage 3 resume.
