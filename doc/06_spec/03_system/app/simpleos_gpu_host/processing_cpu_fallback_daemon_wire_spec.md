# Processing CPU Fallback Daemon Wire Spec

## Purpose

Drive the native SimpleOS GPU host through file-backed shared memory, allow the
HELLO CUDA probe, inject the following CUDA submit failure, and validate the
real fallback receipt.

## Run

Build the host and
`src/app/test/simpleos_gpu_fallback_wire_probe.spl` incrementally, then run:

```sh
sh scripts/check/check-simpleos-gpu-fallback-wire.shs
```

## Checks

1. HELLO completes with CUDA mask `8`.
2. The processing receipt has fallback status `4`, submit reason `16`, CPU
   readback source `2`, requested backend `4`, and exact correlation.
3. Native handle and device identity are zero.
4. All eight readback values equal `0x01020304`; output bytes, exact checksum,
   and elapsed time are validated by the guest bridge.
5. The canonical wrapper fails if either native binary is missing; ordinary
   test discovery marks the native-only row pending. The wrapper bounds the
   complete test/probe run to 60 seconds.

## Current Evidence

The native daemon and probe compile incrementally. The current Linux probe
exits with SIGSEGV before emitting its first marker; live receipt evidence
remains blocked by the tracked native-probe bug.
