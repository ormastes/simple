# Native Vulkan ProcessingIR Fault Contract

## Purpose

Verify the source-matched Simple native Vulkan executor on a real device and
fail closed at every guarded fault phase.

## Run

After incrementally building the probe against a Vulkan-enabled current runtime:

```sh
sh scripts/check/check-processing-vulkan-fault-native.shs
```

The host-independent source contract is:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/processing_vulkan_fault_native_contract_spec.spl \
  --mode=interpreter
```

## Checks

1. Default execution returns eight exact values with positive native handle and
   device identity.
2. Unavailable, init, submit, readback, and mismatch faults return the exact
   typed reason with empty output and zero provenance.
3. Every native process is bounded to 30 seconds and clears inherited
   fault-skip state.
