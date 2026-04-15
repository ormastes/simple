# Pure Simple Torch Standalone TODO

Goal: make Torch/CUDA support a first-class pure-Simple compiler target, not an interpreter/bootstrap fallback path.

## Required

- Preserve `extern fn` imports in compiled `.smf` output.
- Keep Torch ABI names stable for pure Simple:
  - `rt_torch_*` for direct runtime surface
  - `rt_dyn_*` only for explicit dynamic-runtime bridge symbols
- Verify compiled `.smf` resolution through dynamic runtime loading, not just the `pytorch` bootstrap binary.
- Add regression tests for:
  - imported Torch symbol present in generated `.smf`
  - loader resolver invoked for Torch externs
  - compiled pure-Simple upload roundtrip through dynamic runtime

## Cleanup

- Remove interpreter-only fallback dependence from the pure-Simple Torch happy path.
- Merge duplicate Torch upload entrypoints once the compiled ABI path is stable.
- Extend template-aware SMF generation so it also preserves relocations/import symbols.
