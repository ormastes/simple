# ProcessingIR Executor Reason Mapping

## Purpose

Verify the executable reason mapper and the host source integration that routes
typed CUDA, Vulkan, and Metal executor failures toward stable wire reason
codes. Native Vulkan/Metal driver prose stays behind the executor boundary so
wire classification does not depend on driver-vendor error text. End-to-end
daemon wire-slot execution remains a separate open gate.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl \
  --mode=interpreter
```

## Checks

1. Submit/dispatch, readback, and measured offload-overhead wire constants are
   stable and exported (`16`, `17`, and `18`).
2. The mapper executes every stable setup, submit/dispatch, and readback reason
   shape emitted by the CUDA, Vulkan, and Metal executors.
3. Checksum mismatch retains its existing code.
4. Unknown/init failures remain fail-closed as non-device readback.
5. Vulkan and Metal do not expose arbitrary native `last_error` text as the
   executor result reason.
6. The host retains `result.reason`, maps it once, and uses the same mapped
   reason for CPU fallback and hard failure.
7. A strict selector with a zero negotiated processing mask emits unsupported.
8. Every HELLO clears prior negotiated fields before backend probing.

## Current Evidence

- Linux host-independent interpreter contract: 6/6 passed.
- Vulkan importing identity spec: 2/2 passed.
- Metal executor incremental check: passed.
- Native daemon wire-slot and prepared-macOS evidence remain separate gates.
