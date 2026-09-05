# `rt_host_gpu_queue_emit_payload_text` unregistered in self-hosted runner — payload-carrying host↔GPU queue round-trip aborts

## Status
Open.

## Severity
High — breaks the ENTIRE payload-carrying CPU↔GPU queue round-trip in the default
(self-hosted) test runner. Every caller of `rt_host_gpu_queue_emit_payload_text`
aborts with a hard `semantic: unknown extern function` error, so the runtime
backend-handle + payload-hash + `schema=simple-draw-ir-v2` transport cannot be
exercised at all. Regresses 3 pre-existing specs (below).

## Summary
The self-hosted `bin/simple` binary's semantic phase does not know the extern
`rt_host_gpu_queue_emit_payload_text` (6-arg: lane, kind, payload_size,
backend_handle, payload_hash, payload_text). Calling it — directly or transitively
through `engine2d_host_gpu_event_submit_to_runtime_payload_text`
(`src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl:256-268`) — aborts
the `it` block with:

```
semantic: unknown extern function: rt_host_gpu_queue_emit_payload_text
```

The gap is specific to the *payload* emit variant. The 4-arg header-only emit
`rt_host_gpu_queue_emit`, plus `rt_host_gpu_queue_submit` / `_complete` / `_drain`
/ `_reset` / all `_last_*` getters, ARE registered and work (verified: reset →
emit(4-arg) → submit → complete advances real `submitted_count`/`completed_count`
to 1). `rt_host_gpu_queue_emit_payload` (5-arg) is untested but almost certainly
the same gap.

## Evidence
- **Declared** in `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl:139`
  (and gc mirror) as `extern fn rt_host_gpu_queue_emit_payload_text(...)`.
- **Registered in the SEED** rust runtime symbol table:
  `src/compiler_rust/common/src/runtime_symbols.rs:1513` lists
  `"rt_host_gpu_queue_emit_payload_text"`, and it is implemented in
  `src/runtime/runtime_native.c` and `src/compiler_rust/runtime/src/host_gpu_lane.rs`.
  So the SEED accepts it; the self-hosted binary does not — i.e. the pure-Simple
  compiler's extern allowlist / runtime symbol registration is out of sync with the
  seed for this symbol (and likely the 5-arg `_emit_payload`).
- **Regressed specs** (all fail today with the same error):
  - `test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl`
  - `test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
  - `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl` (this is the
    "known pre-existing failure"; the error surfaces after the render pipeline,
    right after `web_render_full_html`, when `html_request_to_pixel_artifact` /
    `dispatch_prepared_draw_ir` reaches the payload emit).

## Impact on new coverage
`test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl` works around this
honestly: the real-runtime round-trip uses the registered header-only emit path
(state machine + counters through the live channel), and the payload-hash / schema
/ backend-handle receipt validation is driven over a synthetic GPU-echoed drain
receipt (the exact struct the runtime returns). The full payload-carrying live
round-trip remains blocked on this bug.

## Leftover DBGPROBE scaffolding (separate, contained)
`src/app/ui.browser/backend.spl:515-570` still has 12 `print "DBGPROBE: ..."`
debug lines in the render path. They are pre-existing leftover scaffolding, owned
by the browser-backend lane, and unrelated to (they merely precede) the extern
abort. They should be removed by that lane; they do not fix this bug and were left
untouched to avoid cross-lane churn.

## Next Step
Register `rt_host_gpu_queue_emit_payload_text` (and `rt_host_gpu_queue_emit_payload`)
in the self-hosted compiler's extern/runtime-symbol set so the pure-Simple semantic
phase accepts them, matching the seed's `runtime_symbols.rs`. Then re-enable the
live payload round-trip assertions (backend-handle 7 echo + `schema=simple-draw-ir-v2`
+ payload-hash) in `host_gpu_queue_roundtrip_spec.spl` and un-regress the three
specs above.
