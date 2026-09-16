# `bin/simple test` reports only the LAST failure per example

**Found:** 2026-08-04, while sabotage-verifying the M6 gen-arena lane.
**Severity:** measurement trap (not a product defect) — it makes sabotage logs
and red-run triage understate what actually broke.
**Binary:** `bin/simple` = Rust seed
(`strings bin/simple | /usr/bin/grep -c "enum construction: unregistered enum"` = 0).

## Behaviour

Two independent facts, both verified with a purpose-built probe:

1. A failing `expect` does **not** abort the rest of the `it` body — execution
   continues through the remaining assertions.
2. The runner prints **one** failure line per example: the **last** failure,
   not the first.

Probe (three examples, all deliberately failing):

| example body | printed |
|---|---|
| `expect(11).to_equal(22)` then `expect(33).to_equal(44)` | `expected 33 to equal 44` (the **second**) |
| `expect(55).to_equal(66)` then `expect(1).to_equal(1)` | `expected 55 to equal 66` |
| `expect(77).to_equal(88)` then `expect(99).to_be_greater_than(100000)` | `expected 99 to be greater than 100000` |

Row 2 shows it is the last *failure* that survives, not the last *assertion*.
Row 1 shows the earlier failure is discarded from the report entirely.

## Why it matters

A sabotage cycle is read by matching the failure message against the defect you
injected. That match can silently fail.

Concrete case: `test/01_unit/os/services/wm/wm_world_gen_arena_stale_handle_spec.spl`
under an injected stale-handle defect. The example asserts, in order:

```
expect(w.window_id_for_handle(stale)).to_equal(0)      # the stale-id check
expect(w.stale_handle_rejections()).to_be_greater_than(0)
```

Both failed. The log showed only `expected 0 to be greater than 0`. Grepping the
log for the expected `expected 4242 to equal 0` returned **zero hits**, which
reads as "the stale-id assertion passed, so my sabotage did not land" — the
opposite of the truth. A deliberately-wrong-oracle probe confirmed the stale
handle really did resolve to 4242.

## Rule

**Count failing examples, not failure messages.** To attribute a specific
assertion, isolate it in its own `it` block, or use a deliberately-wrong oracle
(`expect(v).to_equal(999999)`) so the real value appears in the message.

Related standing traps: bare `assert x == y` in an `it` block is inert (use
`expect` / `assert_true` / `assert_false`); a persistent test daemon freezes env
at daemon start (pass `--no-session-daemon`); only the final
`Results: N total, ...` line is an authoritative verdict.
