# OpenCL Backend Helper CompiledModule Shadowing

Date: 2026-06-04
Severity: p2
Status: open

## Summary

`compile_module_with_backend("opencl", ...)` currently reaches the OpenCL source generation path through `CodegenFactory`, but converting the returned `CodegenOutput` through `to_compiled_module()` is unstable in interpreter-driven tests. The runtime resolves `CompiledModule` through duplicate compiler backend/core names, and attempts to exercise the helper path produced either `class CompiledModule has no field named object_code` or a subprocess exit `-1` after the examples themselves passed.

## Reproduction

Adding an assertion that calls `compile_module_with_backend("opencl", module, false, 0)` from `test/unit/compiler/backend/backend_gpu_target_contract_spec.spl` makes the examples pass but the spec file report:

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
