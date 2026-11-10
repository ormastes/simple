# `TieredJitManager` never tiers up in the interpreter — `compiled` and `call_count` writes are lost, recompilation is unbounded
Status: SUPERSEDED. Triage 2026-11-11 (lane interp4, PR #8185): seed-smoke verified, fixing commit cited in addendum below.

- **Status:** OPEN
- **Filed:** 2026-08-18
- **Severity:** HIGH (unbounded work, wrong dispatch; degrades rather than crashes)
- **Evidence bar:** **SOURCE-VERIFIED, NOT EXECUTION-VERIFIED**
- **Root cause:** `doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
- **Triage:** `scratchpad/sessions/aliasing_unprotected_sites_triage.md` (cluster 3)

## Sites (verified)

`src/lib/nogc_sync_mut/jit/tiered_jit.spl`

| method | bind | lost write(s) |
|---|---|---|
| `try_compile` | 77 | 84 (`hf.compiled = true`), 85 (`hf.jit_handle = ...`) |
| `call_i64`    | 93 | 94 (`hf.call_count = hf.call_count + 1`) |

`HotFunction` is a **class** (`tiered_jit.spl:22`); `self.functions` is a list
field.

## Code shape

```simple
    me try_compile(idx: i64) -> text:
        val hf = self.functions[idx]        # <- COPY in the interpreter
        if hf.compiled:
            return ""
        ...
        if err == "":
            hf.compiled = true              # <- lost
            hf.jit_handle = self.jit_handle # <- lost

    me call_i64(name: text, arg: i64) -> i64:
        val idx = self.find_function(name)
        if idx >= 0:
            val hf = self.functions[idx]    # <- COPY
            hf.call_count = hf.call_count + 1   # <- lost
            if hf.compiled == false:
                if hf.call_count >= hf.threshold:
                    val err = self.try_compile(idx)
```

Note the counters `self.compile_count` / `self.total_compile_us` (lines 86-87)
**do** update — they are `self` fields, the protected path — so the manager's
own statistics keep climbing while the per-function state never moves.

## User-visible symptom

Two compounding failures:

1. `call_count` resets to its initial value on every call, so it can only ever
   reach 1. If any function's `threshold` is greater than 1, **it never
   compiles at all** — the tier-up never fires and everything stays
   interpreted, forever.
2. If a threshold of 1 does let `try_compile` run, `hf.compiled = true` is also
   lost, so the `if hf.compiled: return ""` early-out never triggers and the
   function is **recompiled on every single call** — unbounded native
   compilation work, with `compile_count` and `total_compile_us` growing without
   limit. `hf.jit_handle` is likewise never recorded.

Either way the tiering policy is inert, and the visible signal (a large
`compile_count`) looks like healthy activity rather than a defect.

## Engine matrix

| engine | status |
|---|---|
| tree-walk interpreter | **BROKEN** |
| JIT | correct |
| native | correct |

Interpreter-only: `class` values are represented as `Value::Object`, the
copy-on-write STRUCT carrier, because `Value::ClassInstance` has ZERO producers.
Identity is faked by path-based write-back at ~14 assignment sites, which covers
in-place chained mutation but not bind-then-mutate.

## Minimal repro (from source reasoning, not executed)

```simple
class F:
    hits: i64

class M:
    fns: [F]

impl M:
    me touch():
        val f = self.fns[0]
        f.hits = f.hits + 1

fn main():
    val m = M(fns: [F(hits: 0)])
    m.touch()
    m.touch()
    m.touch()
    print("expect 3, got {m.fns[0].hits}")
```

## Command that would settle it

```bash
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <repro>.spl
SIMPLE_EXECUTION_MODE=jit         bin/simple run <repro>.spl   # control
```

Not run: `bin/simple` is the Rust seed; host saturated by other lanes.

## Reachability

**Not measured.** Interpreter reachability was INFERRED from test references,
not observed. There is an additional irony worth stating rather than assuming
away: a tiered-JIT manager written in Simple is plausibly exercised *under the
interpreter* in tests, but nothing here establishes that it is.

## Correct fix

Engine fix — construct `Value::ClassInstance`. Do **not** add
`self.functions[idx] = hf` write-backs; that masks the engine defect, per the
canonical record.

## 2026-11-10 triage — SUPERSEDED (seed-smoke, lane p3-interp4 row 23)

Root cause is interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17,
verified SUPERSEDED today by lane p3-interp3 (row 14; the 2026-11-04
ClassInstance default-carrier flip holds on the worktree seed). Confirmed by
execution this lane, one cycle, both default and
SIMPLE_EXECUTION_MODE=interpreter:
- `build/p3fix-interp4/row23_tiered_min.spl` (this doc's minimal repro):
  prints "expect 3, got 3" — bind-then-mutate through a class element read
  aliases.
- `build/p3fix-interp4/row23_tiered_manager.spl` (direct TieredJitManager
  driver via std.jit.tiered_jit, threshold=2): prints `calls=-1,42,42`,
  `call_count=3`, `compiled_count=1` — hf.call_count accumulates and tier-up
  fires exactly once; no lost writes, no unbounded recompilation.
No write-back added to tiered_jit.spl (per this doc, the engine fix is
correct — and is now the shipped behavior on this seed). No change from this
lane.
