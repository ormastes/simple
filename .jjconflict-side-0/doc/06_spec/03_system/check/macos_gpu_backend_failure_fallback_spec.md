# macOS GPU Backend Failure and Fallback Receipts

## Purpose

The executable source contract checks the shared Metal/Vulkan failure and
fallback receipt rules on every host, including Linux. It does not synthesize
hardware evidence or claim a runtime PASS. Prepared-macOS execution remains
tracked below.

## Shared Steps

- `step("negotiate processing backend")`
- `step("submit exact processing workload")`
- `step("validate device receipt")`

## Linux Source Contract

Prerequisites: repository checkout, current `bin/simple`, and the `src`
library tree.

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/macos_gpu_backend_failure_fallback_spec.spl \
  --mode=interpreter
```

This runs all source-contract assertions on Linux. It does not execute or
admit prepared-macOS runtime receipts.

## Bounded Metal Child Contract

The companion source
`test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl`
must launch every fault child with `process_run_bounded`, using
`METAL_FAULT_CHILD_TIMEOUT_MS = 30000` milliseconds and
`METAL_FAULT_CHILD_OUTPUT_BYTES = 4194304` (4 MiB). The
`GPU_METAL_FAULT_CHILD_TIMEOUT` marker is required, and unbounded
`process_run("env", args)` is rejected.

## Prepared macOS Runtime Resume

Prerequisites: a current pure-Simple runtime, Metal/Vulkan-capable macOS host,
native provider libraries, and the required platform tools.

```sh
SIMPLE_BIN=bin/simple SIMPLE_LIB=src GPU_2D_LIVE_BACKEND=metal \
  sh scripts/check/check-macos-gpu-2d-live-evidence.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src GPU_2D_LIVE_BACKEND=vulkan \
  sh scripts/check/check-macos-gpu-2d-live-evidence.shs
```

The runtime scenario remains open until these commands produce and
validate native receipts. Linux unavailability, source markers, synthetic
receipts, and CPU fallback are not runtime PASS evidence.

## Retained Artifacts

- `build/tmp/macos_metal_2d_live_evidence/runtime_receipt.env`
- `build/tmp/macos_metal_2d_live_evidence/evidence.env`
- `build/tmp/macos_vulkan_2d_live_evidence/runtime_receipt.env`
- `build/tmp/macos_vulkan_2d_live_evidence/evidence.env`
- `doc/09_report/macos_metal_2d_live_evidence_<UTC>.md`
- `doc/09_report/macos_vulkan_2d_live_evidence_<UTC>.md`
- Native captures, window captures, launch stdout/stderr, and trusted-build
  manifests referenced by each report.

Owner: prepared macOS host operator.

Final reviewer: independent high-capability model.

## Pending-Host Semantics

The source contract is Linux-runnable and records no runtime success. The
actual Metal/Vulkan receipt scenario stays pending until a prepared macOS host
supplies device identity, submission/readback markers, typed failure reasons,
zero failure provenance, and the retained artifacts above.
