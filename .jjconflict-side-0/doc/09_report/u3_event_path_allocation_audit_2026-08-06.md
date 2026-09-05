# U3 — event-path allocation audit: the premise is refuted

- **Date:** 2026-08-06
- **Lane:** U3 (§10.4 / §12.7 U3 of `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`)
- **Verdict:** the OS event path is **already allocation-free per event**, except one
  unavoidable carrier construction at ingress. No `drain_into`, no POD
  `InputPacket`, and no re-plumbing was implemented, because the cost the plan
  targets is not there.
- **Engine identity:** all measurements from `bin/simple` →
  `bin/release/x86_64-unknown-linux-gnu/simple`, md5
  `ed53cc5f255e269ca27c4cd83b17aef9` — the **Rust bootstrap seed**. Probed under
  both the default JIT and `SIMPLE_EXECUTION_MODE=interpret`.

## What the plan claimed

> "the ring is preallocated but the PATH is not allocation-free — allocating
> drains, and per-layer event object construction, recreate the overhead."

Both halves are false for the path that actually runs.

## Claim 1 — "allocating drains": REFUTED (dead code, not a live cost)

`InputEventQueue.drain()` **does** allocate, exactly as described —
`input_event.spl:112-121` builds `var out: [HostInputEvent] = []` and `.push`es
in a loop.

But it has **zero production callers.** A tree-wide search for `.drain()` under
`src/os/` returns nothing; the only caller anywhere is its own spec at
`test/01_unit/os/drivers/input/input_event_queue_spec.spl:125`.

The compositor never uses it. It uses `pop()`, one event per frame, and that is
deliberate — `compositor.spl:1098-1115` documents that applying a whole drained
batch would overwrite up to 63 pending WM pointer steps before the shell could
read one, turning a click into a lost event and a drag into a teleport.

**So the allocating drain is not on the hot path and never was.** It remains a
loaded gun for a future caller (see *Recommendation*).

## Claim 2 — "per-layer event object construction": REFUTED

No layer re-wraps the event. It is constructed **once**, at ingress, and matched
in place from then on:

| step | site | allocations |
|---|---|---|
| PS/2 → carrier | `host_input_adapt.spl:134-157` | **1** — the `HostInputEvent` itself |
| carrier → ring | `input_event.spl:67` `self.buf[self.tail] = ev` | 0 — indexed store into a preallocated slot |
| ring → consumer | `input_event.spl:76` `val ev = self.buf[self.head]` | 0 — indexed read |
| consumer → state | `compositor.spl:1116` `_apply_host_event` | 0 — `match` + scalar field mutation, **no new event object** |

The showcase path is the same shape: `showcase_core.spl:314-317` polls one event
at a time and matches it directly at `:245/:272/:278` — **no intermediate list,
no re-wrapping.**

**Total: 1 allocation per event, at ingress, and it is the carrier itself.**

Removing that last one means replacing the `HostInputEvent` enum with a POD
packet — a cross-cutting change to the single ingress type, explicitly out of
scope here, and of unproven value given it is one construction per *hardware
event*, not per layer.

## Probe evidence

`InputEventQueue` behaves identically on both engines — the indexed store into a
class-field array **persists**, so the ring genuinely stores events rather than
silently dropping writes to a value copy:

```
after_push_len=3
fifo_order=P11,22,b1,w0|K65,'a',true|P33,44,b0,w3|
after_pop_len=0
drain_len=2
drain_after_count=0
overflow_len=256
overflow_dropped=44
oldest_kept=R0x0
```

Byte-identical output under the default JIT and under
`SIMPLE_EXECUTION_MODE=interpret`, both `EXIT=0`.

This mattered enough to measure rather than assume: arrays are value types and
class-field assignment value-copies under the interpreter
(`doc/08_tracking/bug/class_field_reference_semantics_diverge_2026-08-06.md`), so
a plausible failure mode was that every `push` copied the 256-slot array or lost
the write entirely. It does neither — `me` methods mutate the receiver in place
on both engines. The F1 divergence covers a class instance held as *another
class's field*, which is not this shape.

`overflow_dropped=44` (300 pushed, 256 capacity) with `oldest_kept=R0x0` also
confirms the documented drop-**new** policy: a burst never corrupts already-queued
history.

## What genuinely does not exist

Separate from allocation, these §10.4 mechanisms have **no implementation
anywhere in the tree** — a search for `RouteToken`, `route_token`,
`owner_generation`, and `coalesce` returns only the compiler's unrelated
`null_coalesce`:

- **`RouteToken` and stale-generation rejection.** Nothing rejects an event
  aimed at a stale scene or a dead owner.
- **Event coalescing.** Pointer-move and wheel are not coalesced; correspondingly,
  nothing enforces that down/up, key, text, focus and close are *never* coalesced.

These are missing *features*, not allocation problems, and they are the part of
§10.4 worth building. They were not built here because this lane's directive was
scoped to the allocation claim, which turned out to be unfounded — building
routing machinery on that mandate would have been scope drift.

## Recommendation

1. **Delete `InputEventQueue.drain()`** (and fold its spec into `pop`-based
   coverage), or keep it and mark it non-ISR/non-frame explicitly. Today its
   docstring says "Allocates: not ISR-safe" but nothing prevents a future frame
   path from calling it — which is exactly how the plan came to believe it was
   already on the hot path.
2. **Re-scope U3** to what is actually absent: `RouteToken` + stale-generation
   rejection + the coalescing policy. The allocation half of U3 is done, by
   construction, and needs no work.
3. Treat "1 carrier allocation per hardware event" as the measured floor. Any
   future POD-packet proposal should have to beat that number with evidence, not
   with the assumption that the current path allocates more.

## Honest limits

- No heap instrumentation was used. "Allocation" here means *a construction site
  in the source* — enumerated by reading every step of the path — not a measured
  byte count. A runtime allocation counter would be needed to claim bytes.
- Every number is from the **Rust seed**. No self-hosted build exists in this
  tree.
