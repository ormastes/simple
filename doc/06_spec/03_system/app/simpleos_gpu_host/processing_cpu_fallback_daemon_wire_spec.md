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

Run source-matched retained-session device evidence:

```sh
SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm \
  SIMPLEOS_GPU_HOST_BIN=build/simpleos_gpu_host/device_warm_wire/simpleos_gpu_host-source-matched \
  SIMPLEOS_GPU_FALLBACK_WIRE_PROBE_BIN=build/simpleos_gpu_host/device_warm_wire/fallback_wire_probe \
  sh scripts/check/check-simpleos-gpu-fallback-wire.shs
```

`device-warm` explicitly enables `--processing-verify-cpu` and requires eight
CPU/device comparison records. To measure the production path without the
duplicate CPU workload, use:

```sh
SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm-production \
  SIMPLEOS_GPU_HOST_BIN=build/simpleos_gpu_host/device_warm_wire/simpleos_gpu_host-source-matched \
  SIMPLEOS_GPU_FALLBACK_WIRE_PROBE_BIN=build/simpleos_gpu_host/device_warm_wire/fallback_wire_probe \
  sh scripts/check/check-simpleos-gpu-fallback-wire.shs
```

Production mode requires the daemon's explicit
`HOST_GPU_DAEMON_VERIFY processing_verify_cpu=false` startup receipt and fails
if the daemon emits any `HOST_GPU_PROCESS_PERF` record.

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
    and non-device-overhead timings. Evidence mode includes the daemon's CPU
    oracle and comparison; production mode excludes both.
12. Evidence mode requires exactly eight `HOST_GPU_PROCESS_PERF` records.
    Every record must contain positive CPU and device times. Production mode
    requires an explicit verifier-disabled startup receipt and zero comparison
    records.
13. Production FillU32 validation and wire copy use one runtime pass. A wrong
    value returns mismatch before a successful device receipt is published.

## Current Evidence

The six-example source contract passes 6/6. Fallback receipt validation
previously passed 13/13. The source-matched daemon (`1 compiled, 212 cached`)
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
compiled, 215 cached, 0 failed`.

A source-complete strict rebuild (`4 compiled, 213 cached, 0 failed`) then
produced a `string_core` object with zero primitive self-relocations and zero
jump-to-self bodies. Platform-owned render probing removed the next
trait-erased shutdown fault and rebuilt strictly with `4 compiled, 213 cached,
0 failed`. The checksum-corrected probe also rebuilt with `4 compiled, 15
cached, 0 failed`. Its preserved first CUDA receipt has PASS status, zero
reason, device readback, positive handle/identity, exact correlation, and
`4,194,304` bytes, but the output value is 8x the payload. Retained-cache
rebuilds using `words[5] as u32` (`3 compiled, 214 cached`) and an ABI-exact
`raw_read_i32` payload read (`2 compiled, 215 cached`) both preserved that
result. The rebuilt diagnostic probe proves the receipt itself is valid and
only checksum/output parity fail. A fresh 217-module daemon then exposed a
trait-erased `Engine2D.shutdown()` crash during HELLO; concrete retained-backend
shutdown rebuilt at `2 compiled, 215 cached` and restored the valid CUDA
receipt. Fresh-cache disassembly shows tagged `[u32]` slots being loaded as
unboxed values in the old per-pixel wire loop. Source now uses one
runtime-owned bulk copy+checksum call, whose focused Rust unit passes. The
specialized CUDA/Vulkan runtime exports that helper, and the isolated daemon
relinks with `4 compiled, 213 cached, 0 failed`.

The exact device-warm wrapper passes all three warmups plus five measured
1,048,576-element requests: checksum `809508928`, first output word `16909060`,
positive stable handle/identity, exact correlation, and no fallback. Medians
are `155110 us` device, `312012 us` round trip, and `156902 us` non-device
overhead. The measured-request CPU median is `82097 us`, and all receipts are
correctly classified `available-not-preferred`.

Before the startup-mode receipt became mandatory, the retained bulk-readback
daemon passed evidence mode with medians `116663 us` device, `236498 us` round
trip, and `119835 us` non-device overhead, then production mode rejected its
CPU comparison records with `unexpected-cpu-verification`. That daemon predates
both the optimization and `HOST_GPU_DAEMON_VERIFY`, so the strengthened wrapper
now rejects it earlier with `daemon-verifier-mode-mismatch`. These values are
historical repeat baseline evidence, not current-checker or optimized evidence.

A fresh source-matched production daemon remains blocked. Stable-input,
non-admitted Stage3 candidate
`c2a638a51df632e27352543a458289e857c16bfefd79e020bcce39c608f6870a`
clears the prior multiline parser failure. Its retained daemon logs report
relative resolution of `common.ui.draw_ir`, degradation of
`Simple2dDrawIrPlan` to `ANY`, and, in another retained log, an empty native
module-name collision. Diagnose
`native_entry_closure_common_import_type_loss_2026-07-27.md`, build the daemon
incrementally, and rerun `device-warm-production`; no bootstrap is required by
this measurement plan.

The fused copy/validation runtime unit passes 1/1 and the policy source
contract passes 10/10. Runtime ABI manifest/generated symbol-table tests pass,
and strict-probe capsule SHA-256
`6eadbb64103830416faea595cf6c1df328f9a46ac48e5e764d0a1e7512b8a0b0`
exports both checksum helpers. Its strict no-stub, entry-closure-pruned
pure-Simple native smoke passes exact copy/checksum, mismatch, and extra-length
rejection. Provenance-bound Stage3
`af6a3e1b19156793bba13f7294ba60319cca1c31abdfffed68a7f49472f862e9`
still fails at the same `draw_ir_adv.spl:847` parser boundary. The macOS host
provider's formerly empty class body now has the canonical explicit
`create()` constructor; its focused parse check and selector contract pass.
