# Pure-Simple native-build crashes while loading sources

## Status

Open. This blocks updated Simple/LLVM AOT execution evidence for the Engine2D
SIMD row scheduler. Cross-compiled runtime binaries pass on x86-64, AArch64,
and RV64GCV; the crash occurs before MIR or LLVM generation.

## Reproducer

```sh
build/bootstrap-simd-stage4/simple native-build \
  --source test/fixtures/compiler --source src/lib --entry-closure \
  --entry test/fixtures/compiler/llvm_simd_row_native_probe.spl \
  --backend llvm --target x86_64-unknown-linux-gnu --mode one-binary \
  --cache-dir build/check/simd-row-stage4-x86-cache \
  --output build/check/simd-row-stage4-x86
```

Observed on 2026-07-13: exit 139 with no compiler diagnostic. The independent
`build/bootstrap-simd-stage3/simple` artifact fails identically.

## Backtrace

```text
SIGSEGV
CompilerDriver.load_sources_impl
CompilerDriver.compile
compiler_driver_run_compile
cli_native_build
main
```

The next fix should make `load_sources_impl` return a source-loading error
instead of dereferencing an invalid module/source handle. Do not use the Rust
seed as production evidence or retry bootstrap loops to bypass this crash.
