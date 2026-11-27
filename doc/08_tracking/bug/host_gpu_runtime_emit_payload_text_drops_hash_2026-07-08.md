# Bug: `rt_host_gpu_queue_emit_payload_text` does not persist the emitted `payload_hash` (drain reads it back as 0)

- **ID:** host_gpu_runtime_emit_payload_text_drops_hash_2026-07-08
- **Severity:** P3 (silent: the runtime host/GPU queue's text-emit variant
  accepts a `payload_hash: i64` argument but never stores it; a subsequent
  `runtime_drain` returns `last_payload_hash == 0`. The payload *text* is
  persisted and round-trips correctly, so consumers that verify content by
  re-hashing the recovered bytes are unaffected — but any consumer that trusts
  the runtime to carry the emitted hash for an identity/integrity check silently
  sees 0.)
- **Backend:** Rust seed runtime (`rt_host_gpu_queue_emit_payload_text` /
  `rt_host_gpu_queue_last_payload_hash`), reached via
  `engine2d_host_gpu_event_submit_to_runtime_payload_text` →
  `engine2d_host_gpu_runtime_emit_payload_text`
  (`src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl:139,150,177-178,309-320`).
  Reproduced in interpreter mode on macOS aarch64.
- **Status:** FIXED (verified 2026-11-11, lane rt3) — the Rust seed runtime now
  stores the emitted `payload_hash` and returns it after drain; verified on the
  fresh seed (build 46fe8f6b6def). See the 2026-11-11 addendum at the end.

## Symptom

Emit a Draw-IR packet through the runtime host/GPU queue with a nonzero
`payload_hash`, then drain:

```
submit = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane_result, sealed.payload_hash, sealed_text)  # payload_hash != 0
drain  = engine2d_host_gpu_runtime_drain(queue, 1)
# drain.last_payload_text == sealed_text      (CORRECT — bytes persisted)
# drain.last_payload_hash == 0                (WRONG — expected sealed.payload_hash)
```

The i64 `payload_hash` that immediately precedes the `text` argument in the FFI
signature is dropped, while the `text` payload after it survives. The shape
(scalar-before-text lost, text kept) is consistent with a seed FFI
arg-marshalling defect in the text-variant emit path, in the same family as the
other seed marshalling bugs (`bug_u8_cast_push_marshalling`).

## Repro

`test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl` — the
"routes a sealed draw-IR payload through the runtime queue to COMPLETED" case
originally asserted `drain.last_payload_hash == sealed.payload_hash` and failed
with `expected 0 to equal <hash>`.

No pre-existing spec asserted the runtime-carried `last_payload_hash` after a
text emit (`draw_ir_runtime_queue_spec` / `host_gpu_event_queue_spec` check
counts, backend handle, and text, not the hash), so the gap was previously
unobserved.

## Workaround (in Simple, active)

Do not trust the runtime to carry the hash. Re-derive content identity from the
recovered bytes via the pure seal:

```
val recovered = engine2d_host_gpu_seal_draw_ir_payload(drain.last_payload_text)
# recovered.payload_hash == original sealed.payload_hash  -> identity preserved
```

This is strictly stronger than trusting a runtime-carried scalar: it proves the
actual bytes that came out of the queue hash to the same content identity that
went in, independent of the runtime's hash bookkeeping.

## Fix direction (seed)

In the Rust seed, `rt_host_gpu_queue_emit_payload_text` should store the
`payload_hash` argument into the same queue-packet field the non-text variant
(`rt_host_gpu_queue_emit_payload`) uses, so `rt_host_gpu_queue_last_payload_hash`
returns it after drain. If the root cause is arg-marshalling (scalar lost when a
`text` arg follows), the ABI lowering for mixed scalar+text extern calls needs
the fix instead.

---

## 2026-11-11 — Lane rt3 triage verdict: FIXED

**Fixing change:** PR #7597 (merge `9e7e7a526edb`, 2026-11-07) added the full
`payload_hash` plumbing to the Rust seed runtime
(`src/compiler_rust/runtime/src/host_gpu_lane.rs`): the `payload_hash` field on
`HostGpuQueuePacket`, its storage in `rt_host_gpu_queue_emit_payload_text`
(which the non-text `rt_host_gpu_queue_emit_payload` now delegates to), its
propagation to `last_payload_hash` in `complete_packet`, the
`rt_host_gpu_queue_last_payload_hash()` getter, and a Rust unit test asserting
`last_payload_hash() == 42`. The fix is an ancestor of the current seed build
commit `46fe8f6b6def` (2026-11-10). The C runtime
(`src/runtime/runtime_native.c:1316-1337,1437`) carries the same fix for the
native lane.

**Verification (seed-smoke, `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
... --mode=interpreter --no-cache` on build 46fe8f6b6def):**
- Direct extern repro (emit with `payload_hash=424242`/`777`/`555` on lane
  HOST/GPU, submit, drain): `rt_host_gpu_queue_last_payload_hash()` returns the
  emitted value every time (was 0 before the fix).
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl`
  3/3 PASS (re-seals the drained bytes and matches the original hash).
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
  4/4 PASS.

**Residual note (not this bug):** on this seed, `simple run` mode marshals
`text` extern args/returns as empty (payload text reads back `""`), while
`simple test` mode round-trips text correctly (sosix asserts
`drain_payload_text == payload` and passes). The `payload_hash` (i64) marshals
correctly in BOTH modes. This run-mode text quirk is a separate seed
marshalling defect and does not affect the hash fix above.
