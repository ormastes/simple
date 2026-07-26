# ProcessingIR Executor Reason Mapping

## Purpose

Verify the executable reason mapper and the host source integration that routes
typed CUDA, Vulkan, and Metal executor failures toward stable wire reason
codes. End-to-end daemon wire-slot execution remains a separate open gate.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/processing_ir_executor_reason_mapping_contract_spec.spl \
  --mode=interpreter
```

## Checks

1. Submit/dispatch and readback wire constants are stable and exported.
2. The mapper executes exact cases for all three backend reason shapes.
3. Checksum mismatch retains its existing code.
4. Unknown/init failures remain fail-closed as non-device readback.
5. The host retains `result.reason` and passes it through the mapper.
6. A strict selector with a zero negotiated processing mask emits unsupported.
7. Every HELLO clears prior negotiated fields before backend probing.
