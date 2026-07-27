# Processing CPU Fallback Daemon Wire Spec

## Purpose

Drive the native SimpleOS GPU host through file-backed shared memory, allow the
HELLO CUDA probe, inject the following CUDA submit failure, and validate the
real fallback receipt.

The same harness also drives repeated device-success requests through one
daemon-owned CUDA executor.

## Run

Build the host and
`src/app/test/simpleos_gpu_fallback_wire_probe.spl` incrementally, then run:

```sh
sh scripts/check/check-simpleos-gpu-fallback-wire.shs
```

Run retained-session device evidence:

```sh
SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm \
  SIMPLEOS_GPU_HOST_BIN=build/simpleos_gpu_host/device_warm_wire/simpleos_gpu_host \
  SIMPLEOS_GPU_FALLBACK_WIRE_PROBE_BIN=build/simpleos_gpu_host/device_warm_wire/fallback_wire_probe \
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
   probe to 60 seconds by default, keeps the daemon guard 10 seconds longer,
   and waits up to five seconds for the daemon's transport-ready marker.
7. `SIMPLEOS_GPU_FALLBACK_WIRE_MIN_OFFLOAD_ELEMENTS` and
   `SIMPLEOS_GPU_FALLBACK_WIRE_EXPECT_REASON` reuse the same wire harness for
   reason `16` failure injection and reason `18` calibrated policy evidence.
8. The Linux GPU runtime retains the canonical OpenCL provider and shared SIMD
   hit counters through the supported runtime symbol table.
9. HELLO and request publication use separate monotonic budgets. Production
   rendering keeps the 50-million-poll default; diagnostics may request the
   250-million-poll absolute cap, while every request also has a five-second
   deadline.
10. Device-warm mode emits eight correlated CUDA device receipts: three
    warmups and five measured 1,048,576-element requests.
11. Every device readback value and checksum is exact, handle and identity stay
    stable, and the five measured samples produce median device, round-trip,
    and non-device-overhead timings. Non-device overhead includes the daemon's
    CPU oracle, validation, comparison, wire wait, and shared-memory write.

## Current Evidence

The six-example source contract is retained but was not executed because the
available staged pure-Simple compiler has no `test` command. Fallback receipt
validation previously passed 13/13. The source-matched daemon (`1 compiled, 212 cached`)
and final probe (`1 compiled, 18 cached`) complete both native rows: calibrated
small-request reason `18`, and threshold-`0` CUDA submit-failure reason `16`.
Both receipts have CPU source `2`, zero handle/identity, 32 bytes, and checksum
`135272480`.

The device-warm probe builds strictly with `1 compiled, 18 cached, 0 failed`,
no generated stubs, and its three-case median self-test passes. Reusing
`rt_bytes_to_text` and byte snapshots removed unavailable scalar/byte method
dependencies, and strict daemon cycle 2 linked with `4 compiled, 213 cached, 0
failed`. A focused Rust runtime test for the missing string predicate passes;
the refreshed CUDA/Vulkan archive exports it, and cycle 3 links with `2
compiled, 215 cached, 0 failed`. The retained generated `string_core` object
still contained same-named primitive self-dispatch, leaving startup in an
infinite `str_len` loop before transport readiness. Source now routes all
affected primitives directly to runtime externs, but the three-cycle cap was
reached before rebuilding that complete fix. Therefore no daemon device
receipt or warm median is claimed yet.
