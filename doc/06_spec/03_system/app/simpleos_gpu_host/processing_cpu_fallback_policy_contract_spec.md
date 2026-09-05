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
2. The calibrated minimum offload size defaults to `1,048,576`; `0` disables
   policy bypass and malformed values fail CLI validation.
3. With CPU fallback enabled, work below the threshold publishes the CPU oracle
   before device timing/submission with stable reason `18`. Exact-threshold and
   larger work continue to the requested device.
4. Strict fallback `none` always continues to the requested device.
5. Executor failure and output mismatch retain their existing fallback paths.
   Production FillU32 output validation is fused with the runtime-owned wire
   copy/checksum pass; it does not scan the million-element result twice.
6. The CPU oracle is published with fallback status, CPU readback source, the
   original GPU reason, and zero native handle/identity.
7. The runtime helper returns `-1` for any equal-length wrong value and a
   positive checksum only for an exact-length fill. Empty, extra-length, and
   out-of-range ABI inputs return `0`.
8. The guest validator requires exact generation/run/frame/backend correlation
   and rejects forged device provenance.

## Current Evidence

- Host-independent policy contract: 10/10 passed.
- Focused fused runtime copy/validation unit: 1/1 passed.
- Runtime ABI manifest and generated symbol-table tests pass for both checksum
  helpers.
- The refreshed GPU runtime capsule has SHA-256
  `0efd7e3f0f8e2aeda7eb5720df5c67717348772b56bc29ba4f6efaa174591658`
  and exports both native symbols.
- A pure-Simple Stage3 native probe passes exact checksum `50727180`, exact
  readback, mismatch `-1`, and extra-length rejection `0`.
- Native malformed threshold: exit `2` with the expected diagnostic.
- Native calibrated 8-element request: exact CPU fallback receipt with reason
  `18`, source `2`, zero handle/identity, 32 bytes, and checksum `135272480`.
- Native threshold `0` does not return reason `18`; HELLO succeeds, but the
  request-wait timeout prevents retained evidence from identifying the backend.
