# Vaporware/Audit Risk: Orphaned accel_* and proof_* files with fabricated FFI sit unquarantined

- **Date:** 2026-07-06
- **Severity:** MEDIUM (live audit/onboarding hazard, low runtime risk)
- **Area:** src/lib/gc_async_mut/gpu/engine2d/backend_accel_*.spl, backend_*_proof*.spl

## Summary

Six files define fabricated backend simulations with fictional FFI data (`backend_accel_cuda.spl`, `backend_accel_metal.spl`, `backend_accel_vulkan.spl`, `backend_cuda_proof.spl`, `backend_webgpu_proof.spl`, `backend_webgpu_proof_runtime_ops.spl`). These do not implement `RenderBackend` and are never wired into `engine.spl`'s backend selection or Draw-IR executor. Their only "coverage" is two identical spec files that inline-copy the fake classes rather than importing and exercising the real ones. Zero integration wiring, zero external references beyond self-duplication. Primary hazard: they mislead audits/onboarding about the existence of working CUDA/Metal/Vulkan/WebGPU implementations.

## Evidence

- **CudaAccelBackend (fake):** `backend_accel_cuda.spl:143-151` hardcodes device pointer `0x10000000` in `init()`; zero FFI calls anywhere in file; does not implement `RenderBackend` trait
- **MetalAccelBackend (fake):** `backend_accel_metal.spl` similarly fabricates data with no real dispatch
- **VulkanAccelBackend (fake):** `backend_accel_vulkan.spl` same pattern
- **backend_cuda_proof.spl:** declares `extern fn` symbols (`rt_cuda_alloc_fb`, `rt_cuda_clear`, etc.) that do **not exist** in `src/compiler_rust/interpreter_extern/gpu_cuda.rs` (confirmed by direct grep against the real backend's externs)
- **backend_webgpu_proof.spl + runtime_ops:** declares `rt_webgpu_create_device`, `rt_webgpu_submit`, etc. with signatures that mismatch the real `backend_webgpu.spl` externs (e.g. `rt_webgpu_present(handle)->bool` in proof vs. `->text` in real backend); zero implementation in Rust runtime
- **Zero dispatch wiring:** `engine.spl:430-459` (`detect_best_backend()` loop) and `engine.spl:323-412` (`probe_backend()`) contain zero references to `CudaAccelBackend`, `MetalAccelBackend`, `VulkanAccelBackend`, or the proof classes
- **Zero external consumers:** grep for `CudaAccelBackend`, `backend_cuda_proof`, `MetalAccelBackend`, `VulkanAccelBackend` in `.spl` source code (excluding .d fingerprint files) returns zero matches outside the definition files themselves and two isolated spec files
- **Self-duplicating specs:** `backend_accel_proof_spec.spl` and `backend_proof_spec.spl` redeclare inline copies of the fake classes rather than importing and testing the real ones

## Failure scenario

1. Maintainer or auditor reads `backend_accel_cuda.spl` and `backend_cuda_proof.spl` during codebase review
2. Assuming these are working implementations or forward-looking stubs, spends time reverse-engineering them or building on them
3. Discovers they are orphaned/disconnected from real dispatch only after significant analysis
4. Future contributor might assume accel_* pattern is the "right way" to add a new backend and build on it rather than the real `RenderBackend` trait

Low runtime risk: they are never called by production code. High audit/onboarding risk.

## Fix direction

**Option A (delete):** remove `backend_accel_*.spl`, `backend_*_proof*.spl`, and their associated specs (`backend_accel_proof_spec.spl`, `backend_proof_spec.spl`). The real backends (`backend_cuda.spl`, `backend_metal.spl`, `backend_webgpu.spl`) already provide the implementations needed.

**Option B (quarantine + mark):** move all six files to a clearly-marked `_archive/` or `_experimental/` subdirectory with a `README` explaining they are historical or forward-looking simulations, not live implementations. Update import paths in any remaining specs.

**Option A recommended** given zero external coupling and the audit-hazard burden they impose.

## Verification targets

- Backend selection and Draw-IR execution paths do not reference any `accel_*` or `proof_*` class names
- If files are deleted: `bin/simple test` and `bin/simple check` pass without reference errors
- If files are quarantined: a `README` in the quarantine directory explains their status; specs update their imports
- Codebase audit tools (grep, symbol-table) do not mistakenly identify the fake files as active implementations
