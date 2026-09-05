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

1. Default execution returns 64 exact values with positive native handle and
   device identity, and the native text hash passes the known `"abc"` vector.
2. Unavailable, init, submit, readback, and mismatch faults return the exact
   typed reason with empty output and zero provenance.
3. Every native process is bounded to 30 seconds and clears inherited
   fault-skip state.
4. One process injects a submit failure, clears the target through the
   canonical environment facade, and then completes an exact device request.
5. Each process merges stdout and stderr and emits exactly one anchored native
   or recovery receipt; an otherwise valid receipt cannot hide a contradictory
   second receipt on either stream.
6. Storage-buffer download inserts a compute-shader-write/transfer-write to
   transfer-read buffer barrier before the staging copy.

## Current Evidence

The Vulkan-enabled runtime archive rebuilds incrementally, and the strict
current-source recovery probe links with `1 compiled, 28 cached, 0 failed`.
The wrapper passes one exact 64-value device receipt, all five typed fault
phases, and one same-process submit-failure recovery sequence. Success reports
`hash_sanity=true`, handle/identity `666008366`, and exact values; each fault
reports its expected reason, empty output, and zero provenance. The recovery
sequence records a successful device receipt, arms the fault, receives zero
provenance, clears the fault through the canonical environment facade, and
returns the same identity and values without exiting.

The checker now requires exactly one fully anchored receipt from every child.
The focused source contract passes 3/3, and the current recovery artifact
passes the stricter live wrapper when selected through
`PROCESSING_VULKAN_FAULT_PROBE_BIN`.

After adding the explicit storage readback barrier, the focused runtime mask
unit passes 1/1. A strict no-stub, entry-closure probe relink against runtime
archive SHA-256
`5c7c5cf5eda02bf5e81816f80e135c257da5aecd1392fcc596beeb54e797d3b5`
passes the canonical live wrapper: one exact 64-value receipt, all five typed
faults, and submit-failure recovery retain RTX A6000 identity `666008366`.
Compute and transfer submissions use the same mutex for their intentionally
shared `VkQueue`, preserving Vulkan's external-synchronization requirement.

The selected identity matches the host's NVIDIA RTX A6000 driver/device
properties. Runtime-owned UTF-16 hashing avoids converting selected-device
metadata through tagged native text arrays. The compatibility facade, runtime
symbol registry, codegen declaration, and interpreter registration compile
together in the focused Cargo check. Retained logs, explicit source manifests,
the selected-device property tuple, and artifact hashes are bound by
`build/simpleos_gpu_host/vulkan_fault_native/evidence-provenance-current-source.env`.

Retained recovery evidence:
`build/simpleos_gpu_host/vulkan_fault_native/build-recovery-cycle2.log` and
`wrapper-recovery-cycle2.log`. `evidence-provenance-recovery.env` binds the
explicit source manifest, runtime archive, probe, wrapper log, and selected
identity.
