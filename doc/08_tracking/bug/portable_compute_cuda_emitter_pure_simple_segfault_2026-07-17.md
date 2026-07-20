# Portable-compute CUDA emitter crashes in the pure-Simple runtime

**Status:** Open
**Date:** 2026-07-17
**Owner:** compiler / portable compute

## Symptom

The canonical CUDA portable-compute evidence check cannot regenerate the
font-atlas PTX after the common blending semantics changed from version 1 to
version 2. The admitted pure-Simple release binary segfaults while running
`src/app/portable_compute_emit/main.spl`; the generated source is empty and the
checker correctly fails closed.

## Reproduction and evidence

Run `scripts/check/check-portable-compute-toolchains.shs` with only the CUDA
target enabled and a fresh build directory. Retained evidence is in:

- `build/portable_compute_toolchains/cuda_semantics2_baseline/cuda_source.err`
- `doc/09_report/portable_compute_toolchains_cuda_semantics2_baseline_2026-07-17.md`

The report records `generated_source_failed` for both CUDA artifacts. The host
has CUDA 13.0.88 `nvcc`; generation fails before the CUDA compiler is invoked.

## Required fix

1. Reproduce and repair the pure-Simple emitter crash without falling back to
   the Rust seed or hand-editing generated PTX.
2. Add a focused regression that emits non-empty CUDA source for the
   font-atlas composition program.
3. Regenerate and independently review CUDA source/PTX and provenance.
4. Atomically update the embedded PTX, source/program/PTX hashes, semantics
   version, checker pins, and trust tests.

## Root-cause diagnosis (2026-07-18)

A focused native emitter probe crashed before its first `main` statement. The
native backtrace stopped at
`startup.launch_metadata.startup_normalize_program_args`; disassembly of the
deployed CLI shows its typed `args.len()` loading offset 8 from the masked
empty-list value before testing the tag. Current Rust LLVM lowering already
guards zero masked pointer bits before the load
(`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`), but the
deployed CLI does not contain that guard. This is therefore a stale deployed
compiler binary, not CUDA-source construction or hashing. The focused CUDA
probe is `test/01_unit/compiler/codegen/portable_compute_emitter_native.spl`.

Post-fix execution is intentionally pending: this lane's two-execution cap was
consumed by the reproducer and its GDB backtrace. Rebuild/redeploy the
pure-Simple CLI from current compiler sources, run the focused probe once, then
resume canonical semantics-v2 regeneration.

A current Rust bootstrap-seed interpreter diagnostic exits 0 and emits a
2,017-byte optimization module, a 1,862-byte font kernel, and four 64-character
SHA-256 strings. This isolates the remaining failure to stale pure-Simple
deployment, but is not accepted as pure-Simple or CUDA toolchain evidence.

## Acceptance

- The pure-Simple emitter exits successfully and produces non-empty source.
- CUDA compilation and validation pass with semantics version 2.
- The tracked backend passes its provenance/trust check.
- Device readback covers translucent destination alpha and matches the common
  composition result.
