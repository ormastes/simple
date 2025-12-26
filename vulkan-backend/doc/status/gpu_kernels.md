# Feature #126: GPU Kernels (`#[gpu]`)

**Status**: Not implemented (planned, see `doc/plans/26_gpu_kernels.md`)  
**Difficulty**: 5  
**Importance**: 5

## Summary
Add `#[gpu]`-annotated kernel functions, lower them to SPIR-V, and provide host APIs to launch kernels with device buffers.

## Current State
- No parser/semantic support for `#[gpu]`.
- No SPIR-V lowering or runtime launch plumbing.
 - HIR lowering explicitly rejects `#[gpu]` functions with a clear diagnostic so usage fails fast.

## Next Steps
- Implement attribute parsing and kernel subset validation.
- Add SPIR-V builder/lowering pipeline and emit kernel blobs.
- Provide host launch API and feature-flagged runtime integration.
