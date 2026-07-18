# CUDA font companion lacks a production package trust anchor

Date: 2026-07-15

Status: trust anchor implemented; retained CUDA device readback pending (2026-07-16)

## Impact

The pure-Simple portable emitter and checker generated and authenticated a CUDA
font PTX which is now source-tracked with immutable hashes. Engine2D validates
and attempts that companion during CUDA construction without reading mutable
ignored `build/` output or disabling primitive CUDA when the active driver
cannot load the font PTX.

## Evidence

- `scripts/check/check-portable-compute-toolchains.shs` writes PTX and its
  self-reported SHA-256 under `build/portable_compute_toolchains`.
- `Engine2D.install_cuda_font_artifact` checks payload/hash consistency,
  program version, bounds, and the versioned entry before session mutation.
- `PackageVerify` explicitly skips checksum verification and assumes success.
- `package/build.spl` still returns `checksum_placeholder`.

The artifact and its adjacent evidence share one mutable producer; neither
supplies an independent production trust decision. The embedded Vulkan font
artifact is the closest valid pattern, but a CUDA equivalent needs a retained,
Simple-generated PTX and pinned digest before it can be tracked honestly.

## Completion criteria

1. A package manifest or generated tracked module binds the PTX bytes to an
   immutable expected SHA-256 and `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`.
2. The trust owner computes and compares the real digest before exposing bytes
   to Engine2D; mismatch and missing metadata fail closed.
3. The package/bootstrap owner passes authenticated bytes to the canonical
   Engine2D CUDA construction path without environment reads or `build/` path
   discovery inside the library.
4. Static tamper tests and retained CUDA device-origin readback prove the
   packaged path. CPU replay remains authoritative when the companion is absent
   under Suggested/Preferred policy; Required policy fails closed.

Do not solve this by embedding handwritten PTX, trusting an adjacent evidence
file, or adding a second font renderer, cache, or kernel.

## Fresh-session resume

After deploying a current pure-Simple self-hosted binary, run this once from the
repository root on the NVIDIA host:

```sh
CUDA_ARCH=compute_75 SIMPLE_BIN=bin/simple \
  sh scripts/check/check-portable-compute-toolchains.shs
```

Accept the generation input only when `evidence.env` reports
`cuda_font_status=compiled_artifact_verified`, the exact versioned font symbol,
and current Simple invocation/runtime plus emitter/source/artifact SHA-256 rows.
The adjacent hash remains test provenance; independently pin the accepted PTX
in its package manifest or tracked generated module before factory installation.

## 2026-07-16 bounded attempt

The CUDA checker was run once with the freshly linked Stage4 CLI and fixed
`CUDA_ARCH=compute_75`. It failed before `nvcc`: the requested emitter spec
crossed from the canonical C array runtime into a localized Rust
`rt_cli_run_tests` closure, decoded as an empty argument list, and entered the
unfocused test runner. No PTX or acceptable artifact hash was produced.

The final permitted Stage4 rebuild terminated with SIGSEGV before producing a
log or binary, so the session's three-cycle cap was reached. Higher-model
review then refined the source repair to a scalar-only runtime entry which
reads canonical C argv through the existing `spl_arg_count`/`spl_get_arg`
scalar/raw ABI, avoiding the mixed-runtime container ABI while preserving
inherited stdio and GC flags. Parser and interpreter-registration tests passed
during refinement; the final link remains pending because the runtime criterion
had already reached its three-cycle cap. No rebuilt Stage4 runtime evidence
exists for this source shape. Do not pin or embed a CUDA payload from this run.

Resume in a fresh session by rebuilding Stage4 once, first proving
`SIMPLE_BOOTSTRAP_DRIVER=/bin/echo <candidate> test SENTINEL.spl` prints both
`test` and `SENTINEL.spl`, then running the checker once. If it reports
`cuda_font_status=compiled_artifact_verified`, mirror
`backend_vulkan_font_spirv.spl`: add one tracked generated CUDA PTX module,
pin the exact source/version/artifact hashes, install through
`Engine2D.install_cuda_font_artifact`, and extend the existing CUDA unit/system
specs rather than creating a parallel renderer, cache, kernel, or verifier.

## 2026-07-16 continuation

The bootstrap `libsimple_runtime.a` was refreshed successfully and now exports
`rt_cli_run_tests_process_args`. A single cache-preserving Stage 4 rebuild from
the verified Stage 3 compiler reproduced the pre-log SIGSEGV, emitted no
candidate, and did not modify the 1,164-object cache. No core was retained.
The CUDA checker was therefore not rerun and the trust-anchor criteria remain
unchanged.

## 2026-07-16 debugger evidence

A cache-preserving debugger run captured the pre-log SIGSEGV in
`LLVMModuleCreateWithNameInContext`, specifically at
`llvm::DataLayout::setAlignment`, from `LlvmBackend::create_module`. This is the
observed crash site, not yet a proven root cause. The initial eight-worker trace
showed multiple LLVM module constructors. A one-worker rebuild still failed
deterministically while compiling
`examples/10_tooling/trace32_tools/cmm_lsp/cmm_ast.spl`, so `--threads 1` is not
a workaround. A final one-worker full-CLI build omitted `examples/10_tooling`
entirely and still SIGSEGV'd before useful logging, binary output, or any change
to the 1,164-object cache. The tooling closure is therefore not necessary to
trigger the defect.

These three bounded isolation variants exhausted the session cap. Diagnose and
repair the compiler/backend defect, then rebuild the current Stage 3/Stage 4
chain before resuming the scalar-argv sentinel and CUDA checker. Do not
generate, pin, or install CUDA PTX until the current full CLI passes that
sentinel.

## 2026-07-16 trust-anchor implementation

A stable pure-Simple emitter app produced the CUDA source without the test
runner. `nvcc 13.0.88 --ptx -arch=compute_75` compiled the tracked companion;
its PTX SHA-256 is
`40afab945e6c40c239a6859d63723e76599758ea50e120e0edf7a058aa6922b4`.
Runtime construction checks the PTX hash, exact versioned entry, and common
program version. The checker and focused SPipe bind the pinned source and
emitter-version hashes exactly to a fresh Simple emission. Criteria 1-3 are
implemented; criterion 4 remains open until the canonical runner and retained
CUDA device-origin readback pass.
