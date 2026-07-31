# Direct CUDA ProcessingIR Fill Contract

## Purpose

Prove that `processing_ir_execute_cuda` executes the shared
`FillU32(0x01020304)` fixture on a CUDA device without CPU fallback. The
default parity mode uses 64 elements; large mode uses the calibrated
1,048,576-element policy threshold. Warm mode executes that threshold twice
through one retained `CudaSession`.

## Run

Build `src/app/test/processing_cuda_fill_probe.spl` incrementally against the
CUDA-enabled runtime, then run:

```sh
sh scripts/check/check-processing-cuda-fill-native.shs
```

Run the threshold workload against the same candidate:

```sh
PROCESSING_CUDA_FILL_MODE=large \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

Run the retained-session timing check:

```sh
PROCESSING_CUDA_FILL_MODE=warm \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

Run same-process readback-failure recovery:

```sh
PROCESSING_CUDA_FILL_MODE=recovery \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

Run same-process submit-failure recovery:

```sh
PROCESSING_CUDA_FILL_MODE=recovery-submit \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

Run same-process checksum-mismatch recovery:

```sh
PROCESSING_CUDA_FILL_MODE=recovery-mismatch \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

The recovery mode names and typed failure reasons are:

| Mode | Injected phase | Required failure reason |
| --- | --- | --- |
| `recovery` | `readback` | `cuda-readback-failed` |
| `recovery-submit` | `submit` | `cuda-submit-failed` |
| `recovery-mismatch` | `mismatch` | `checksum-mismatch` |

Each mode is a single-process sequence: an exact baseline call, one injected
failure with empty output and zero provenance, then an exact recovery call on
the same executor. The recovery call must preserve the positive backend handle
and device identity from the baseline.

## Checks

1. Every returned value exactly matches `0x01020304`.
2. Expected and actual checksums equal `1082179840` in parity mode or
   `17730434498560` in large mode.
3. Mismatch count is zero.
4. Device handle and identity are positive.
5. End-to-end executor time is positive.
6. The receipt names CUDA device readback and rejects CPU fallback.
7. Readback materialization uses the runtime-owned bulk
   `rt_u32s_from_raw` conversion, not a per-element `push` loop.
8. Warm mode requires the second exact device request to complete faster than
   the cold request through the same executor.
9. `recovery` requires exact baseline output, a post-sync `cuda-readback-failed`
   result with empty output and zero provenance, then exact output with the
   same positive handle and device identity.
10. `recovery-submit` requires the typed `cuda-submit-failed` result with empty
    output and zero provenance, then exact output with the same positive handle
    and device identity.
11. `recovery-mismatch` requires the typed `checksum-mismatch` result with
    empty output and zero provenance, then exact output with the same positive
    handle and device identity.

## Current Evidence

The retained native candidate passes both modes with exact checksums, zero
mismatches, positive handle/identity, device readback, and no CPU fallback.
The 1,048,576-element run improved from `1044501 us` with per-element
materialization to `593323 us` with the canonical bulk converter. The retained
session run completed cold in `861499 us` and warm in `69331 us`, a 12.4x
improvement, with exact values and unchanged device provenance. Those timings
precede the subsequent retained-context activation repair; its two-context
runtime test passes, but the capped Simple probe was not rebuilt a fourth time.
Correlated daemon-wire and multi-sample evidence remain open.

The 2026-07-27 recovery candidate
`10323c8438ed987a2610793aa6af680933ae20e933ce0f3c11fcdbc281259519`
passes baseline/failure/recovery in one process. Baseline and recovery each
return 64 exact values with checksum `1082179840`, handle `1`, and device
identity `1002905313239842438`; the injected synchronized readback failure
returns `cuda-readback-failed`, zero values, zero handle, and zero identity.
The same candidate also passes ordinary parity mode.

The `recovery-submit` and `recovery-mismatch` modes are documented contract
coverage for the corresponding typed fault paths. No execution evidence for
those modes is recorded in this manual yet; they have not been run for this
spec update.
