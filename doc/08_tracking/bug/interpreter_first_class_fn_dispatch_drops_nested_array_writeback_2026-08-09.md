# Interpreter: two mutating `me` calls inside one first-class-function-dispatched invocation drop the first write

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
(compiler/interpreter internals, out of scope for the application-level task
that found it).
**Engine:** tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) —
reproduced without any JIT involvement.
**Date filed:** 2026-08-09
**Found while investigating:** the "Follow-up" section of
doc/08_tracking/bug/lab_http_api_spec_never_completes_via_test_daemon_2026-08-08.md

## Symptom

```
struct Item:
    id: text
    events: [text]

class State:
    items: [Item]

    static fn create() -> State:
        State(items: [])

    me add_item(id: text):
        self.items.push(Item(id: id, events: []))

    me push_event(idx: i64, e: text):
        var it = self.items[idx]
        it.events.push(e)
        self.items[idx] = it

var S: State = State.create()

fn route_create():
    S.add_item("x")

fn route_execute():
    S.push_event(0, "a")
    S.push_event(0, "b")

fn direct_events_check():
    print "events_len={S.items[0].events.len()}"

fn dispatch(f):
    f()

dispatch(route_create)
dispatch(route_execute)
direct_events_check()
```

Run with `SIMPLE_EXECUTION_MODE=interpreter bin/simple run <file>`. Expected:
`events_len=2`. Actual: `events_len=1` — one of the two `push_event` calls'
writes is silently lost.

## Isolation

- A **single** `push_event` call inside `route_execute` (only `"a"`, no
  `"b"`) persists correctly (`events_len=1`, no loss).
- **Two separate `dispatch()` calls**, each doing one `push_event`, both
  persist correctly (`events_len=2`).
- **Two `push_event` calls inside one dispatched function** lose one write.
- Combining both frames into a **single mutating method call**
  (`push_events(idx, [e1, e2])`, one call that does two `.push()`es inside
  the one method) fixes it — `events_len=2`.
- Adding a **second, different** mutating method
  (`record_cell(idx, ...)` then `push_events(idx, ...)`, i.e. two different
  methods, each still one call, back to back in one dispatched invocation)
  reproduces the loss again, but now the FIRST call's write is the one that
  survives and the SECOND's is lost (`cells_len=1`, `events_len=0` — not
  merely "one of two frames", the whole second write vanished).

The common trigger: **more than one mutating `me` method call, each doing
its own read-modify-writeback of the same array element, issued from inside
a single invocation of a function that was itself called through a stored
first-class function value** (`f()` where `f` is a parameter/variable
holding a function, not a direct `name()` call). Calling the outer function
directly (not through `dispatch(f)`) does not reproduce this — module
top-level statements calling named functions directly persist all
mutations correctly regardless of how many mutating calls are chained.

This exact shape (`Router.dispatch` calling `r.handler(req)` where `handler`
is a stored `fn(HttpRequest) -> HttpResponse` field —
`src/lib/nogc_sync_mut/http_server/router.spl:76`) is used by every HTTP
route in this repo's hand-rolled servers (`app.simple_lab.lab_server`,
`app.ui.web.server`, and others), so any handler that performs two or more
sequential mutating method calls against the same nested array element is
at risk.

## Repro files

Ephemeral repro scripts used during isolation were written to
`/tmp/claude-1000/.../scratchpad/repro_arr_mut*.spl` during the investigating
session and are not checked in; the snippet above is sufficient to reproduce
from scratch. Reproduced against `bin/release/x86_64-unknown-linux-gnu/simple`
(the Rust bootstrap seed banner is printed by every run; not yet verified
against the pure-Simple self-hosted binary since `bin/simple` currently
resolves to the seed on this host — see `.claude/rules/bootstrap.md`).

## Relationship to the bigger, still-open defect

This narrower defect is **not sufficient** to explain the full failure in
`lab_http_api_spec.spl`'s second `it` block: collapsing the real server's
two mutating calls (`record_cell` + `push_events`) into one combined method
call fixes this narrower symptom in isolation, but the real server's event
buffer still reads back as empty on the *next accepted TCP connection* even
after that fix (see the "Follow-up" section of
`lab_http_api_spec_never_completes_via_test_daemon_2026-08-08.md` for the
full escalation, including a flat-top-level-array restructure that also did
not help). That points at an additional, broader defect specific to state
crossing a real `TcpListener.accept()` boundary in a spawned server
subprocess, which this narrower in-process repro does not reproduce.

## Further investigation (2026-08-09, second pass) — confirmed real, found BROADER and more erratic than filed; no fix attempted

Reproduced the doc's exact minimal repro verbatim against
`bin/release/x86_64-unknown-linux-gnu/simple` (still the only binary available
on this host; `bin/simple` still resolves to this same seed) with
`SIMPLE_EXECUTION_MODE=interpreter`: confirmed `events_len=1`, matching the
filed symptom exactly.

However, probing the "Isolation" section's specific claims with small
variants turned up behavior that **contradicts** that section and shows the
defect is not narrowly scoped to "two mutating calls in one dispatched
invocation":

- The doc claims *"A single `push_event` call inside `route_execute` ...
  persists correctly"*. Reproduced verbatim (`route_execute_one` calling
  `push_event` once) — confirmed, `events_len=1`, write persists.
- But a structurally similar single-call, single-dispatch case for
  **`add_item`** alone (`dispatch(route_create)` calling
  `S.add_item("x")` once, nothing else) **does not persist**: `S.items.len()`
  reads back as `0`, not `1`, immediately after the dispatch returns.
- Same total loss for a plain scalar field mutated once through dispatch
  (`me inc(): self.n = self.n + 1`, single `dispatch(route_execute)` call,
  no arrays at all): `S.n` reads back as `0`, not `1`.
- Same total loss for a bare `self.items.push(x)` on a `[text]` field (no
  nested struct, no read-modify-writeback via index assignment), single
  dispatch call: `S.items.len()` reads back as `0`.
- Yet in the full original repro, `add_item`'s write (called first, via its
  own `dispatch()`) **does** end up visible by the time the final
  `direct_events_check()` runs — otherwise `events_len` couldn't read `1`
  (indexing `S.items[0]` would panic/fail on an empty list).

Put together: whether a given dispatched mutating call's write is visible
depends on more than "how many mutating calls happened inside one dispatched
invocation" — it also seems to depend on what runs *after* it (a later
dispatch call, a later direct top-level statement/function call that reads
the same variable), on the field's static type (struct list vs. scalar vs.
primitive list), and on whether the read-back happens through a nested
index expression or a direct field read. This is consistent with the bug
doc's own theory (a stale environment snapshot for `self`/module globals,
captured at some point and clobbering real state on writeback) but the
snapshot/flush point is evidently not simply "per dispatched call" — it
looks tied to some other, still-unidentified trigger (possibly a lazy
env-flush that only happens on certain subsequent variable reads or scope
exits). Repro files used for this pass (`scratch_repro2.spl` through
`scratch_repro8.spl`) were ephemeral, written under the worktree used for
this investigation and not checked in; each is a 15-20 line variant of the
snippet above and can be reconstructed trivially from the bullets.

**Conclusion: no fix attempted.** The interpreter's module-global /
`self`-writeback visibility around first-class-function dispatch is
evidently a broad, poorly-understood area — the actual trigger condition is
not what the original isolation described, small structural changes flip
the outcome unpredictably, and I could not pin a specific flush/snapshot
function or file:line as the root cause in the time available. Per this
repo's standing guidance (interpreter is fragile, has caused repeated
regressions, "fix .spl not Rust" bias, and this task's own instruction to
not attempt a fix without high confidence in a narrow root cause), this is
left open rather than risking a partial/wrong Rust interpreter change. A
real fix will need dedicated tracing of the interpreter's environment
snapshot/writeback machinery for module-level `var` bindings referenced by
`me` methods invoked through a first-class function value — start by
instrumenting `place.rs` / `node_exec.rs` for wherever module-global
variable slots are read and re-written around a call to a value held in a
function/closure binding, and check whether that env is a snapshot copy
(cloned) vs. a shared handle (`Rc<RefCell<..>>`), and at what point (if any)
a cloned copy gets written back to the shared slot.

## Suggested next step

1. Reproduce this file's minimal repro directly (no HTTP/sockets needed) to
   confirm before investing further.
2. Instrument the interpreter's handling of stored function values
   (whatever represents `f` when passed as a parameter and invoked via
   `f()`) to see whether it captures/restores an environment snapshot for
   `self`/module globals on entry, and whether that snapshot is captured
   once at binding time or per-call — the "second call's write is lost"
   pattern is consistent with the second call operating against a
   snapshot taken before the first call's write landed, then that stale
   snapshot's writeback clobbering the real state.
3. Separately investigate the accept()-boundary state loss described in
   the parent bug doc — it survives even a single combined mutating call,
   so it is a distinct (likely larger) defect from this one.

## Re-investigated 2026-08-10 (independent verification, binary-provenance-based)

Reproduced the exact minimal repro fresh (no HTTP/sockets) against the
currently deployed `bin/simple`: `SIMPLE_EXECUTION_MODE=interpreter bin/simple
run` on the doc's verbatim snippet still prints `events_len=1`, matching the
filed symptom exactly.

`readlink -f bin/simple` / `bin/simple --version` confirm the deployed binary
is the Rust bootstrap seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
seed warning banner). `/usr/bin/grep -rl "Closure\|FnValue\|first.class"
src/compiler/95.interp/` and a listing of the pure-Simple interpreter tree
(`mir_interpreter.spl`, `mir_interp_ops.spl`, `mir_interp_intrinsics.spl`,
`interpreter/{operators,pattern}.spl` — 1,856 lines total) turn up **no
first-class-function-value dispatch or closure-call machinery at all**: no
code path represents "a function stored in a variable and invoked via
`f()`" as a distinct case from a direct named call. There is therefore no
editable `.spl` counterpart to the module-global/`self` env-snapshot
machinery this bug implicates — the only implementation that runs the
doc's repro today is the Rust seed's interpreter (environment/place
handling for stored function values, per the "Suggested next step" section
above, not yet localized to a specific seed file:line by this pass either).

Conclusion: legitimate architectural classification, now backed by a
binary-provenance check (deployed `bin/simple` is confirmed seed) and a
structural check of the pure-Simple tree (no closure/first-class-fn dispatch
implementation exists there to fix). The underlying trigger condition
remains genuinely unpinned to a narrow root cause even within the seed —
consistent with the original investigation's conclusion not to attempt a
partial/wrong fix. Status unchanged: **OPEN — ARCHITECTURAL (Rust seed
interpreter, no pure-Simple first-class-fn dispatch implementation exists to
fix instead, verified 2026-08-10)**.

## Re-verification 2026-08-17 — DOES NOT REPRODUCE

Ran the doc's verbatim reproducer — `struct Item`/`class State`, module-global
`var S`, `dispatch(route_create)` then `dispatch(route_execute)` at TOP LEVEL
(not wrapped in `main`, matching the doc exactly) — with
`SIMPLE_EXECUTION_MODE=interpreter` on the deployed seed:

    items_len=1 events_len=2

Expected `events_len=2`; the doc records `1`. Both the nested-array writeback and
the broader `items.len()==0` variant behave. The same shape wrapped inside
`fn main()` also passes, so the top-level-statement form is not a distinguishing
factor either.

Most likely closed by `merge_shared_collection_fields`
(`interpreter_call/core/function_exec.rs:975`): the previous
`is_value_type_struct` gate excluded EVERY value-type struct from
`write_back_mutable_arguments`, which is exactly why a container field nested in
a struct lost its write when the frame popped.

Not proven: the "scalar `me inc()` via dispatch reads back 0" variant from the
second pass was not separately exercised, and
`src/lib/nogc_sync_mut/http_server/router.spl:76` was not re-checked.
