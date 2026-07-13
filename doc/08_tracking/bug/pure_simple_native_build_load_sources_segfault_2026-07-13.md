# Pure-Simple native-build crashes while loading sources

## Status

Partially fixed through stage 8. Pure-Simple native-build now passes entry
closure loading and starts frontend parsing. Updated Simple/LLVM AOT execution
evidence for the Engine2D SIMD row scheduler remains blocked by a later
runtime/frontend failure whose exact cause is not yet classified.
Cross-compiled runtime binaries pass on x86-64, AArch64, and RV64GCV.

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

Follow-up identified the dispatch cause: a host `native-build` without
`--target` is a pure-Simple tool and interprets `src/app/cli/native_build_main.spl`;
it never enters the Rust bootstrap builder. Supplying the real host target
`--target x86_64-unknown-linux-gnu` routes the seed to its bootstrap handler and
starts entry discovery in seconds. That path then exposed a spanless Rust-parser
failure in `src/lib/common/encoding/sfnt.spl`; discovery now reports parser
line/column, and a focused regression covers the compatible SFNT source form.

## Stage-5 evidence

An explicit host target completed the optimized Rust-seed bootstrap build in
244.2 seconds: 1,019 reachable files compiled, zero failed, and
`build/bootstrap-simd-stage5/simple --version` reports `Simple v1.0.0-beta`.
The stage-5 artifact reaches pure-Simple native-build, but the SIMD probe then
reported `function not found: str.split_lines` and exited 139. `split_lines`
is implemented by the Rust interpreter but is absent from native method
registration; `split` lowers to `rt_string_split`. The entry-closure scan now
uses one `content.split("\\n")` pass, preserving the linear scan while using
the supported native ABI.

## Stage-6 through stage-8 evidence

The cache-preserving stage-6 rebuild compiled 3 files, reused 1,016 cached
objects, and linked in 146.2 seconds. Its first native SIMD probe reached
`CompilerDriver.load_sources_impl`, where disassembly identified a null call
through the declared but C-runtime-missing `rt_array_concat` ABI.

The shared C runtime now implements `rt_array_concat` for generic, packed-byte,
packed-u64, and mixed arrays without mutating either input. The existing core-C
ABI probe covers those cases, invalid input, and the exported symbol. That
focused probe passes. Stage 7 then compiled 2 files, reused 1,017 cached
objects, and linked in 155.0 seconds. Its next null call was `rt_array_clear` from
`expr_reset`; the C runtime now implements the same validate-and-reset behavior
as the Rust and simple-core runtimes, with valid and invalid cases in the ABI
probe.

Stage 8 compiled 2 files, reused 1,017 cached objects, and linked in 137.6
seconds. `nm` confirms both `rt_array_concat` and `rt_array_clear` are defined.
The pure-Simple LLVM SIMD probe still exits 139 before emitting a compiler
diagnostic. The mandatory three-cycle cap stopped further rebuilds in this
session; the next bounded continuation should take one debugger backtrace from
stage 8, classify the failure, and resolve only the concrete cause.
