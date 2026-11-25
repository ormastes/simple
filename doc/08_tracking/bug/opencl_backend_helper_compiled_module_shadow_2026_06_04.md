# OpenCL Backend Helper CompiledModule Shadowing

Date: 2026-06-04
Severity: p2
Status: open

## Summary

`compile_module_with_backend("opencl", ...)` currently reaches the OpenCL source generation path through `CodegenFactory`, but converting the returned `CodegenOutput` through `to_compiled_module()` is unstable in interpreter-driven tests. The runtime resolves `CompiledModule` through duplicate compiler backend/core names, and attempts to exercise the helper path produced either `class CompiledModule has no field named object_code` or a subprocess exit `-1` after the examples themselves passed.

## Reproduction

Adding an assertion that calls `compile_module_with_backend("opencl", module, false, 0)` from `test/01_unit/compiler/backend/backend_gpu_target_contract_spec.spl` makes the examples pass but the spec file report:

```text
Error: Process exited with code -1
Passed: 8
Failed: 0
```

A standalone probe confirmed the OpenCL source is generated before teardown:

```text
is_ok=true
source_len=72
__kernel void opencl_dispatch_kernel() {
BB0:
    return;
}
fatal runtime error: stack overflow, aborting
```

## Suspected Cause

There are multiple `CompiledModule` definitions in compiler layers. The generic `CodegenOutput.to_compiled_module()` conversion and backend helper dispatch can bind to a non-artifact `CompiledModule` instead of `compiler.backend.backend.backend_types.CompiledModule`, depending on runtime/module resolution.

## Required Fix

Make backend artifact output use a uniquely named type or a runtime-stable qualified constructor path, then add a clean unit test proving:

- `compile_module_with_backend("opencl", ...)` returns OpenCL C text in `assembly`.
- `compile_module_with_backend("cl", ...)` follows the same path.
- The spec subprocess exits cleanly without `code -1`.

## Triage 2026-11-25 (p2w4-ai lane, release/1.0.0 @ b1a2b76fb64)

- **measured**: the suspected root cause no longer matches the tree. There is
  now exactly ONE `struct CompiledModule`
  (`src/compiler/70.backend/backend/backend_types.spl:399`, with the
  `object_code: [u8]?` field at :402); the former duplicate definitions are
  uniquely named (`CoreCompiledModule`, `CudaCompiledModule`,
  `VhdlCompiledModule`, `VulkanCompiledModule`, `CraneliftCompiledModule`),
  which is the "uniquely named type" fix this entry required. The
  `compile_module_with_backend` helper path is exercised by multiple landed
  specs (`test/02_integration/compiler/llvm_compiled_proof_spec.spl`,
  `llvm_parity_spec.spl`, others).
- **gap**: the specific requested regression — an assertion calling
  `compile_module_with_backend("opencl", ...)` / `("cl", ...)` from
  `backend_gpu_target_contract_spec.spl` proving OpenCL C text in `assembly`
  and a clean subprocess exit — was never added; no spec in the tree calls the
  helper with `"opencl"`/`"cl"`.
- **blocked**: adding and running that test here is not possible: the pinned
  `bin/simple.exe` seed rejects `@representation_boundary` (cfd89933699), so
  no spec executes at HEAD on this host, and the original symptom was exactly
  an interpreter-driven instability that must be executed to confirm gone.
- Verdict: leave OPEN, narrowed — shadowing hazard structurally removed;
  remaining work is the opencl/cl helper regression spec, executed on a host
  with a runnable toolchain.
