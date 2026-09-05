# `SessionManager.remove_breakpoint` returns `true` while the breakpoint stays armed; `set_state` is frozen (interpreter)

- **Status:** OPEN
- **Filed:** 2026-08-18
- **Severity:** MEDIUM-HIGH (actively misreported success in a debugger control path)
- **Evidence bar:** **SOURCE-VERIFIED, NOT EXECUTION-VERIFIED**
- **Root cause:** `doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
- **Triage:** `scratchpad/sessions/aliasing_unprotected_sites_triage.md` (cluster 4)

## Sites (verified)

`src/lib/nogc_async_mut/mcp/session.spl`

| method | bind | lost write |
|---|---|---|
| `remove_breakpoint` | 217 | 219 (`session.breakpoints = session.breakpoints.filter(...)`) |
| `set_state`         | 226 | 228 (`session.state = new_state`) |

`DebugSession` is a **class** (`session.spl:23`); `self.sessions` is a
`Dict`-valued field.

## Code shape

```simple
    fn remove_breakpoint(session_id: String, bp_id: Int) -> Bool:
        if self.sessions.contains_key(session_id):
            val session = self.sessions[session_id]        # <- COPY
            val initial_len = session.breakpoints.len()
            session.breakpoints = session.breakpoints.filter(_1.id != bp_id)  # <- lost
            session.breakpoints.len() < initial_len        # <- reads the LOCAL copy
        else:
            false

    me set_state(session_id: String, new_state: SessionState):
        if self.sessions.contains_key(session_id):
            val session = self.sessions[session_id]        # <- COPY
            session.state = new_state                      # <- lost
```

No `self.sessions[session_id] = session` write-back exists in either method.

## User-visible symptom

`remove_breakpoint` is the sharper of the two: the filter and the length
comparison both operate on the discarded local copy, so the method computes and
**returns `true`** — a truthful statement about the copy — while the session
held by the manager still carries the breakpoint. The debugger reports the
breakpoint removed, the UI stops listing it, and execution still halts there,
with no way for the user to remove it. That is worse than a plain no-op, because
the return value actively certifies the removal.

`set_state` is a plain silent no-op: session state never advances (running /
paused / stopped transitions are all dropped), so any logic that polls session
state observes it frozen at its initial value.

## Engine matrix

| engine | status |
|---|---|
| tree-walk interpreter | **BROKEN** |
| JIT | correct |
| native | correct |

Interpreter-only: class values use `Value::Object`, the copy-on-write STRUCT
carrier, because `Value::ClassInstance` has ZERO producers; identity is faked by
path-based write-back at ~14 assignment sites, which does not cover
bind-then-mutate.

## Minimal repro (from source reasoning, not executed)

```simple
class S:
    marks: [i64]
    state: i64

class Mgr:
    sessions: {text: S}

impl Mgr:
    fn drop_mark(id: text, m: i64) -> bool:
        if self.sessions.contains_key(id):
            val s = self.sessions[id]
            val before = s.marks.len()
            s.marks = s.marks.filter(_1 != m)
            s.marks.len() < before
        else:
            false

fn main():
    val g = Mgr(sessions: {"a": S(marks: [1, 2], state: 0)})
    val ok = g.drop_mark("a", 1)
    print("returned={ok} expect remaining 1, got {g.sessions["a"].marks.len()}")
```

Predicted interpreter output: `returned=true ... got 2` — the return value and
the observable state disagree.

## Command that would settle it

```bash
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <repro>.spl
SIMPLE_EXECUTION_MODE=jit         bin/simple run <repro>.spl   # control
```

Not run: `bin/simple` is the Rust seed; host saturated.

## Reachability

**Not measured.** Interpreter reachability was INFERRED from test references in
the triage, not observed. As with the `TaskManager` row, the dict carrier is a
second unverified step: dict-element copying is reasoned from the shared
`Value::Object` representation, not demonstrated.

## Correct fix

Engine fix — construct `Value::ClassInstance` in the interpreter. Do **not** add
a `self.sessions[session_id] = session` write-back here; that masks the engine
defect rather than fixing it, as the canonical record states.
