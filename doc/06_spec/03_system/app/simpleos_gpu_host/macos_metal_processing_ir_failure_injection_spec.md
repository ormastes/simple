# macOS Metal ProcessingIR Failure Injection

## Purpose

On a prepared macOS Metal host, verify the production executor's default path
and deterministic `unavailable`, `init`, `submit`, `readback`, and `mismatch`
failures.

## Prerequisites

- Current pure-Simple runtime with Metal SFFI
- Available Metal device
- Xcode command-line tools
- `SIMPLE_LIB=src`

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl \
  --mode=interpreter \
  > build/simpleos_gpu_host/gpu_backend_failure_injection_macos.log 2>&1
```

## Checks

1. With both fault variables absent, Metal completes eight exact
   `0x01020304` output elements with checksum `135272480`, `reason=ok`, a
   nonzero handle, and a nonzero device identity.
2. Each injected phase returns its exact typed reason.
3. Every injected failure returns empty output, `values_exact=false`, checksum
   `0`, handle `0`, and identity `0`.
4. Setting only one fault variable leaves injection disabled.
5. Each probe runs in an isolated child environment without re-entering tests.
6. Every child is bounded to 30 seconds and 4 MiB per output stream. A timeout
   emits `GPU_METAL_FAULT_CHILD_TIMEOUT` into the retained test log.

Non-macOS execution records this row as postponed and cannot satisfy the live
Metal gate.
