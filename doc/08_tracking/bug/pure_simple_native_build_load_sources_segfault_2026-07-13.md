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

## Bootstrap rebuild evidence

On 2026-07-13, three bounded attempts used the optimized Rust seed only to
rebuild the pure-Simple CLI with the concrete entry
`src/app/cli/_CliMain/main_and_help.spl`, `--entry-closure`, and the preserved
1,177-object cache. Each attempt timed out after 900 seconds before discovery
or object generation, at about 100% CPU and 1.27 GB RSS. Using one
`--source src` root instead of the three compiler/app/lib roots did not change the
result. With `SIMPLE_NATIVE_BUILD_RUST_TRACE=1`, the final attempt recorded
zero `discover visit` events, zero cache mutations, and no output artifact.

The first attempt exposed invalid nested-JSON brace escaping in
`src/app/stats/doc_coverage_dynamic.spl`; that source now passes the focused
bootstrap check. After that repair, the final build log contained zero parser
errors but still timed out before discovery. The remaining investigation must
instrument the pre-discovery source-analysis phase rather than retry the same
full CLI build.
