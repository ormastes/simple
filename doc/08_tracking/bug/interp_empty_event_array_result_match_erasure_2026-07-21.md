# Interp: empty `[Event]` payload bound via `case Ok(events)` degrades to i64 0

- **Date:** 2026-07-21
- **Status:** OPEN
- **Area:** Rust seed interpreter — Result match-arm binding, empty typed arrays
- **Severity:** medium (silent type degradation; faults on first method call)

## Symptom

`EventLoop.poll(0)` returns `Result<[Event], IoError>`. With no fds registered
the payload is an empty `[Event]`. Binding it through a match arm:

```simple
val pr = lp.poll(0)
match pr:
    case Ok(events):
        events.len()    # semantic: method `len` not found on type `i64` (receiver value: 0)
```

The empty array payload arrives in the arm as **i64 0**, not `[Event]`.

## Repro

`bin/simple run` (seed interp, warning banner) on 2026-07-21, host linux-x86_64.
The decisive variable is the EXECUTION CONTEXT, not the binding form:

- From a plain `fn main` (any import mix, incl. the full UI closure):
  `poll(0).is_ok()`, `poll_one(0)`, and even `case Ok(events): events.len()`
  variants all WORK.
- From inside ANY sspec `it` (minimal spec: just `use std.spec.*` +
  `use std.io.event_loop.{EventLoop}`), `lp.poll(0)` itself faults with
  "method `len` not found on type `i64` (receiver value: 0)" — the failing
  frame is `raw.len()` INSIDE `EventLoop.poll`, where `raw` is the
  platform-event extern's return. Moving the code into a top-level helper
  called from the `it` does NOT help; the degradation follows the spec-runner
  context.

So: under the sspec runner, the extern's empty `[i64]` return arrives as
i64 0; under plain main it arrives as a typed empty array.

Found by `test/02_integration/ui/event_backend_matrix_spec.spl` (EventLoop
smoke). Split per the probe pattern: the spec asserts create/backend/close;
`test/02_integration/ui/probe_event_loop_smoke.spl` is the runnable mirror
covering poll(0)/poll_one(0) until this is fixed.

## Class

Same family as the empty-container element-type erasure fixed on the native
path (`runtime_elem_value_type`, plan
`doc/03_plan/compiler/backend/container_f64_and_native_struct_construct_plan_2026-07-20.md`)
and the known interp quirks (`.?` on 0-i64). The interp's Ok-payload extraction
loses the static element type when the array is empty and hands back the tag-0
scalar instead of an empty typed array.

## Fix direction

Interp `Result`/enum payload extraction should preserve the declared payload
type for empty containers (mirror of the native-side fix). Requires seed
rebuild to verify.
