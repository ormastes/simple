# Processing CPU Fallback Policy Contract Spec

## Purpose

Verify the SimpleOS GPU host's explicit CPU-fallback policy and wire contract
without claiming an end-to-end daemon or native GPU run.

## Run

```sh
SIMPLE_LIB=src bin/simple test test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl --mode=interpreter
```

## Checks

1. Fallback defaults to `none`; only `none` and `cpu` are accepted.
2. CPU fallback is reachable only after executor failure or output mismatch.
3. The CPU oracle is published with fallback status, CPU readback source, the
   original GPU reason, and zero native handle/identity.
4. The guest validator requires exact generation/run/frame/backend correlation
   and rejects forged device provenance.
