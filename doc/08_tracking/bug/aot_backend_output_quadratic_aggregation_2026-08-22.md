# AOT backend output aggregation repeatedly copied completed prefixes

- **Date:** 2026-08-22
- **Area:** Pure-Simple compiler AOT output assembly
- **Status:** Fixed
- **Severity:** medium performance and transient-memory amplification

## Root cause

The single-file C, CUDA, OpenCL, and WASM output paths appended each compiled
module to one immutable text value. For similarly sized modules, each append
copied the entire completed prefix again. Aggregating `N` modules therefore
performed quadratic copy work and temporarily retained both the old prefix and
its replacement.

## Fix

Each backend now stores module output as text fragments and performs one
`join` after code generation. C, CUDA, and OpenCL use an empty separator. WASM
filters empty module output before joining with the historical two-newline
separator, preserving byte-for-byte behavior for leading, trailing, and
interior empty modules.

## Evidence

- `test/01_unit/compiler/driver/aot_output_aggregation_spec.spl` checks exact
  ordering, empty fragments, and WAT separators.
- `test/05_perf/compiler/aot_output_aggregation_perf_contract.spl` measures
  128 versus 256 4-KiB fragments, checks output bytes, and requires bounded
  near-linear N-to-2N scaling.

Measured with the bootstrap-seed test runner against the Pure-Simple source:
524,288 bytes joined in 620 us and 1,048,576 bytes in 518 us. The intentionally
generous contract rejects superlinear regression while tolerating CI timing
noise. The deployed Pure-Simple executable exited 139 before executing either
focused spec; that pre-existing binary failure is not counted as passing
evidence.
