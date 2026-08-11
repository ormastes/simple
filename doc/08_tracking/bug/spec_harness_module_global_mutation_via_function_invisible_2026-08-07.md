# `bin/simple test` cannot see module-global mutation performed inside a called function

## Status: OPEN, not root-caused (found incidentally, out of scope to fix here)

## Summary

Inside a `bin/simple test` spec's `it` block, a module-level `var` that is
mutated by calling a separate `fn` (rather than being assigned inline in the
`it` block itself) reads back as if the mutation never happened. This is
**not specific to `Dict`** -- a plain scalar `i64` global reproduces it
identically -- and it does **not** reproduce under plain `bin/simple run`
(interpreter or JIT), only under the `bin/simple test` spec harness.

## Repro

```simple
use std.spec

var g_n: i64 = 0
var g_x: Dict<text, i64> = {}

fn bump():
    g_n = g_n + 1

fn w1():
    g_x["hits"] = 7

describe "isolate2":
    it "plain scalar global mutated via function":
        bump()
        expect(g_n).to_equal(1)          # FAILS: "expected 0 to equal 1"

    it "dict global mutated via function, bracket only":
        w1()
        expect(g_x["hits"]).to_equal(7)  # FAILS: "expected nil to equal 7"
```

Run: `bin/simple test <file>` -> both `it` blocks fail, in a fresh temp file
with no other module state, using only bracket-assign (not `.set()`) for the
dict case, so this is unrelated to the `.set()` vs `d[k]=v` question this
probe was originally built to test (see
`doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md`).

Control: the exact same source, run via
`SIMPLE_EXECUTION_MODE=interpret bin/simple run <file>` (calling the
functions and printing the values from a `main`, no `describe`/`it`), reads
back the correct mutated values every time. So the interpreter's function-call
and module-global-write semantics are fine outside the spec harness; something
specific to how `bin/simple test` sets up/executes `it` blocks (fresh module
instance per test? re-snapshotted globals? a different call path for
top-level `fn` invocation from inside a describe/it closure?) is the suspect,
not general interpreter correctness.

## Impact / risk

Any spec that relies on a helper `fn` to mutate module-level state and then
asserts on that state in the same or a later `it` block would silently
observe the PRE-mutation value with no error (reads back the zero-value /
`nil`, not a crash) -- a false-negative risk mirroring the Dict-miss "reads
back like a fresh/absent value" class of bug, but at the harness level, and
for `i64` too. Not yet swept for how many existing specs rely on this
pattern; that sweep is future work.

## Not done in this pass

- Root cause in the spec runner / interpreter's `it`-block dispatch is not
  identified. Candidates to check first: whether `bin/simple test` compiles/
  loads each `it` as a fresh top-level entry with a re-initialized module
  globals table, vs. `bin/simple run`'s single module instance for the whole
  file's `main`.
- No fix attempted -- this doc is a find-and-file, not a repro-and-fix, to
  stay within the scope of the task that surfaced it (Dict bracket-vs-set
  parity).
- No sweep of existing specs for reliance on this now-suspect pattern.

## Not a duplicate of the mainless-module compile-lane bug

`doc/08_tracking/bug/compile_lane_false_fails_globals_in_mainless_modules_2026-07-29.md`
covers a different, compile-time symptom: `bin/simple compile` on an
entry-script module with a module-level global but no `fn main()` fails with
`Undefined("undefined identifier: ...")` or an SMF-emission error, because
the compile lane tries to synthesize a `main` from the top-level statements.
This spec harness bug is different in kind: the spec FILE compiles and RUNS
fine (`bin/simple test` produces a `Results:` line, not a compile error) --
the failure is a wrong VALUE read back at runtime inside an `it` block, not a
compile-time failure. Both happen to involve module-level globals in a
`describe`/`it`-shaped (mainless) `.spl` file, which is why they're easy to
conflate, but the mechanisms and fixes are unrelated.

## Related

- `doc/08_tracking/bug/dict_set_bracket_write_parity_2026-08-07.md` (the
  investigation that surfaced this)
- `doc/08_tracking/bug/compile_lane_false_fails_globals_in_mainless_modules_2026-07-29.md`
  (similar-sounding, different mechanism -- see note above)
- `.claude/rules/testing.md` "run and test are DIFFERENT ENGINES"
