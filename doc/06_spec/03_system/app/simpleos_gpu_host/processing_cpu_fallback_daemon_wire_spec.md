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
5. Writable mappings normalize the public `bool` to native ABI `0/1`; the
   probe's `--mmap-smoke` path writes and reads the protocol magic directly.
6. The executable spec checks wrapper/probe ownership and receipt assertions.
   The canonical wrapper fails if either native binary is missing, bounds the
   probe to 60 seconds by default, and keeps the daemon guard 10 seconds longer.

## Current Evidence

Linux host-independent source contract passes 2/2, fallback receipt validation
passes 13/13, and the incrementally rebuilt native mmap smoke writes and reads
the exact protocol word. Two intermediate uncommitted wait variants completed
the expected daemon-wire fallback receipt, but the final bounded cycle exhausted
HELLO before admission. Those wait edits were withdrawn; deterministic native
daemon-wire completion remains open.
