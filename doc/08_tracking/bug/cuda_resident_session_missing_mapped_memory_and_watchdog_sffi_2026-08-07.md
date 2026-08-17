# CUDA resident-session design §5.3 needs 3 missing SFFI bindings: `cuMemHostAlloc`, `cuMemHostGetDevicePointer`, `cuDeviceGetAttribute`

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
SFFI bindings (`cuMemHostAlloc`/`cuMemHostGetDevicePointer`/
`cuDeviceGetAttribute` and their `rt_cuda_*` extern counterparts) are still
absent from `src/lib/nogc_sync_mut/cuda/sffi.spl`
(`grep -n 'cuMemHostAlloc\|cuMemHostGetDevicePointer\|cuDeviceGetAttribute\|rt_cuda_mem_host_alloc\|rt_cuda_device_get_attribute'` → no matches), and
`cuda_resident_session.spl` still uses `unknown_watchdog_attr()` (no
`live_watchdog_attr()` provider added). Re-ran
`test/03_system/gpu_lane/cuda_resident_session_spec.spl` fresh: unchanged,
`Results: 18 total, 18 passed, 0 failed`, same refusal-branch on this
hardware-less host. A genuine fix needs (a) new Rust-runtime C extern
bindings (`src/runtime/`, not vendored, but a real runtime build/adapter
change outside a docs-verification pass) for the three Driver API calls, and
(b) hand-authored, conformance-tested resident ring-polling PTX plus a real
CUDA device to exercise the live branch — none of which is available in this
worktree/host. Left honestly open; the doc's own "Resume" steps remain the
correct next actions.
**Found:** 2026-08-07 (Task B4, gpu_remote_interpreter parallel plan)
**Component:** `src/lib/nogc_sync_mut/cuda/sffi.spl` (CUDA SFFI layer) /
`src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl` (new B4 module)
**Design:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` §5.3
**Attribution:** grep-confirmed absence in the current CUDA SFFI surface
(`src/lib/nogc_sync_mut/cuda/sffi.spl`), same host/build class as B3's filed
gaps (`cuda_available_false_negative_under_native_jit_2026-08-07.md` and
siblings).

## What was found

Design §5.3 (`interpreter(remote(cuda(smNN(resident))))`) requires three CUDA
Driver API capabilities that have no `extern fn` binding anywhere in this
repo's `.spl` CUDA SFFI layer:

1. **`cuMemHostAlloc(MAPPED|PORTABLE)`** — allocates a pinned host buffer the
   device can address directly (via `cuMemHostGetDevicePointer`). Needed so a
   resident kernel and the host servicer thread can both see writes to the
   arena without a `cuMemcpy` round-trip. `sffi.spl` only has
   `rt_cuda_mem_alloc`/`rt_cuda_mem_free` (plain device memory,
   `cuMemAlloc`/`cuMemFree`) — no host-mapped variant.
2. **`cuMemHostGetDevicePointer`** — resolves the device-side pointer for a
   mapped host allocation. Not bound at all.
3. **`cuDeviceGetAttribute(CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_TIMEOUT)`** — the
   watchdog/TDR query design §5.3's refusal gate needs to make its decision
   from real hardware state. Not bound at all (grep for
   `KERNEL_EXEC_TIMEOUT`, `DeviceGetAttribute`, `device_attribute` across
   `src/lib/` and `src/runtime/` turns up nothing CUDA-related).

Additionally, no checked-in PTX artifact implements a **resident,
ring-polling kernel** — the only checked-in CUDA SVM-G entry point is B3's
`svmg_interpret` in `src/lib/gc_async_mut/gpu_lane/svmg_cuda_kernel.ptx`,
which is per-launch (one SGP program, one launch, exits). A true design §5.3
resident kernel would need to loop reading the 8-slot command ring via
`cuda::atomic_ref<uint32_t, thread_scope_system>` on mapped memory — that PTX
does not exist yet, and hand-authoring it is out of scope for this task
(would need its own conformance pass against the D2 host reference VM, same
rigor as B3's `svmg_interpret`).

## Impact

`src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl` (Task B4) therefore
implements the parts of design §5.3 that ARE expressible today, fully:

- The 8-slot command-ring / doorbell protocol state machine
  (`CommandRing`) — pure host-side bytes, unit-tested, no gap.
- The watchdog refusal gate (`resident_refusal_gate`) — pure, unit-tested,
  no gap in the DECISION logic itself.
- The interactive servicer (`InteractiveServicer`, driving A2's
  `service_trigger`) — real, unit-tested against a simulated device
  (`arena.fire_command`), no gap in the SERVICING logic itself.

But it CANNOT exercise any of these against a real resident/interactive CUDA
dispatch:

- `unknown_watchdog_attr()` always returns `WATCHDOG_UNKNOWN` on this build
  (no way to ask the real device), so `resident_refusal_gate`'s fail-safe
  policy refuses every live start unless the operator sets
  `CUDA_RESIDENT_FORCE=1` — which papers over a REAL watchdog device just as
  much as a non-watchdog one. There is no way, today, to correctly and
  automatically distinguish "safe to run resident" from "will get TDR-killed"
  on live hardware.
- `ResidentSession.run_program` falls back to B3's per-launch dispatch
  (`CudaVmExecutor.run_source`) internally — one open session across N
  programs (satisfies "resident SESSION"), but each program is still a
  separate kernel launch/sync/drain, not a single long-running kernel serviced
  live mid-execution. PUTC order across programs is correct (sequential
  execution), but PUTC delivery WITHIN one program's execution is buffered
  (drained after sync), not truly live/interleaved with the host servicer
  thread as design §5.3 intends.

## Verified (2026-08-07, this host — no CUDA device)

`bin/simple test test/03_system/gpu_lane/cuda_resident_session_spec.spl`:
`Results: 18 total, 18 passed, 0 failed`. All 17 host-independent examples
(refusal gate x6, command ring x7, interactive servicer x4) exercise real
logic with no gap. The 18th example (">=3 programs through ONE resident
session") takes the refusal/skip branch on this host — `start()` returns
`refuse:cuda-resident-watchdog-attr-unavailable` because
`unknown_watchdog_attr()` always reports unknown and `CUDA_RESIDENT_FORCE` is
unset — and the spec asserts that refusal explicitly rather than papering
over it as a pass.

Sabotage probe (same session): inverting `resident_refusal_gate`'s
`WATCHDOG_ENABLED` check to `WATCHDOG_DISABLED` turned 2 of the 6
refusal-gate examples RED (`6 examples, 2 failures`); reverting restored
`18 total, 18 passed, 0 failed`.

## Resume

1. Add `rt_cuda_mem_host_alloc`/`rt_cuda_mem_host_free` and
   `rt_cuda_mem_host_get_device_pointer` externs (Rust runtime +
   `interpreter_extern` adapter, same two-layer pattern as
   `rt_cuda_module_load_data_bytes`'s fix) to `sffi.spl`.
2. Add `rt_cuda_device_get_attribute(device, attribute_id)` bound to
   `cuDeviceGetAttribute`; expose
   `CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_TIMEOUT`'s numeric ID (75 in the CUDA
   Driver API) as a named constant in `sffi.spl`. Wire a real
   `live_watchdog_attr()` provider in `cuda_resident_session.spl` to replace
   `unknown_watchdog_attr()` as the default once available.
3. Author and check in a resident ring-polling PTX kernel (own conformance
   pass against D2's `ref_vm`, mirroring B3's `svmg_cuda_kernel.ptx`
   provenance), then swap `ResidentSession.run_program`'s per-launch fallback
   for a true single-launch ring-serviced dispatch.
4. Re-run `test/03_system/gpu_lane/cuda_resident_session_spec.spl` on a real
   CUDA host with `CUDA_RESIDENT_FORCE` unset (real watchdog query should now
   decide correctly without forcing) to get the live branch (currently
   refused/SKIPped everywhere) actually exercised.

## Reproduce

```
bin/simple test test/03_system/gpu_lane/cuda_resident_session_spec.spl
```
