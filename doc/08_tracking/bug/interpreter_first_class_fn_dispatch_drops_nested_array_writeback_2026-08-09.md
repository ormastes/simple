# Interpreter: two mutating `me` calls inside one first-class-function-dispatched invocation drop the first write

**Status:** OPEN — root-caused with a minimal, sockets-free repro; not fixed
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
