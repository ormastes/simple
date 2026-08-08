# CUDA and Vulkan ProcessingIR Failure Injection

## Purpose

Exercise the production CUDA and Vulkan executors with process-isolated,
disabled-by-default failure injection.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl \
  --mode=interpreter
```

## Checks

1. With both fault variables absent, neither backend reports an injected
   failure.
2. `unavailable`, `init`, `submit`, `readback`, and `mismatch` return exact
   typed reasons with empty values and zero provenance.
3. Injection requires both `SIMPLE_GPU_TEST=1` and an exact
   `SIMPLE_GPU_FAULT_INJECT=<backend>:<phase>` selector.
4. Each case runs in a clean child environment.

The current Linux runtime may postpone Vulkan phases that require the missing
`rt_vulkan_dependency_quarantine_lock` extern. CUDA remains a hard live gate.
