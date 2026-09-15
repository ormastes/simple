# BUG: a write inside `after_each` that reads the captured variable is lost; a constant write is not

## Re-measured 2026-09-13 — reproduces, but the TITLE IS WRONG: the constant write is lost too

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`),
Windows, via `SIMPLE_BINARY=<abs> simple test <spec>`. The spec harness runs the
**interpreter** lane here (verified in the same run with a `print "{not nil}"`
probe, which prints `true`; the JIT prints `false` — see
`not_over_nil_returns_false_in_run_engine_2026-08-04.md`).

Probe: the entry's own hook, two warm-up examples so `after_each` fires twice,
then the two captured values asserted in **separate** examples:

```
describe "closure capture probe":
    var flag = false
    var counter = 0
    after_each:
        flag = true                 # constant write
        counter = counter + 1       # read-modify-write
    it "warm1":   expect 1 to_equal 1
    it "warm2":   expect 1 to_equal 1
    it "flag":    expect flag to_equal true
    it "counter": expect counter to_equal 2
```

```
  ✓ warm1
  ✓ warm2
  ✗ flag        expected false to equal true
  ✗ counter     expected 0 to equal 2
Results: 5 total, 3 passed, 2 failed
```

**Both writes are lost.** The reported asymmetry — "a constant write is not
[lost]" — does not hold: `flag` is still `false` after two hook firings.

This correction matters because the asymmetry was the entry's main diagnostic
clue and it is an artifact of how the original probe was read. Asserting `flag`
and `counter` in the *same* `it` reports only one failure line, and it is the
`counter` one; that reads as "flag passed" and it is not. Any future probe of
this defect must assert each captured variable in its own example.

With the asymmetry gone the defect is simpler than filed: **no** write performed
inside an `after_each` hook is visible to the enclosing `describe` scope.

Entry stays OPEN. Not fixed here — the hook/closure capture path is in the seed
(`src/compiler_rust/**`), off-limits during this pass (concurrent bootstrap).

**Possibly related, with a stated difference.**
`top_level_array_index_assign_in_loop_silently_dropped_2026-08-25.md` (also
re-characterised 2026-09-13) has the same outward shape: a body demonstrably
runs while its writes to an enclosing scope vanish, silently, exit 0. Now that
the asymmetry here is gone the two look *more* alike, not less. The remaining
difference to check before assuming one mechanism: the module-scope defect
discards the loop's control variable too (`i == 0` after `while i < 3`, yet the
program terminates), i.e. the enclosing scope never sees any effect at all,
whereas an `after_each` hook here is at least *invoked* the right number of
times. Same family, plausibly; not proven identical.
**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — spec hooks silently fail to accumulate state, so any
`after_each`/`before_each` counter is stuck at its initial value. No error.
**Files:**
- failing spec: `test/01_unit/std/feature_validation/testing_framework_spec.spl:136-145`
  (+ legacy duplicate under `test/unit/std/`)

## Symptom

Probe `/tmp/probe_closure_spec.spl`, run with
`bin/simple test ... --no-cache --no-cover-check`:

```
describe "closure capture probe":
    var flag = false
    var counter = 0

    after_each:
        flag = true
        counter = counter + 1

    it "first example":
        expect(flag).to_equal(false)

    it "second example sees after_each mutation":
        expect(flag).to_equal(true)      # PASSES  — constant write propagated
        expect(counter).to_equal(1)      # FAILS   — "expected 0 to equal 1"
```

```
✗ second example sees after_each mutation
  expected 0 to equal 1
Results: 2 total, 1 passed, 1 failed
```

Both statements are writes to a `var` captured from the enclosing `describe`,
in the same hook, one line apart. `flag = true` is visible in the next example.
`counter = counter + 1` is not — `counter` reads back as `0`.

The in-repo case, `testing_framework_spec.spl:136-145`:

```
var cleanup_flag = false

after_each:
    cleanup_flag = true

it "runs test before cleanup":
    expect(cleanup_flag).to_equal(false)     # passes

it "verifies after_each runs":
    expect(cleanup_flag).to_equal(true)      # FAILS: expected false to equal true
```

## Root cause

Not pinned to a file:line — and the obvious explanation does not fit, which is
why this is filed rather than guessed at.

`CLAUDE.md` (`.claude/rules/language.md`, "Runtime Limitations") states: *"Nested
closure capture - can READ outer vars, CANNOT MODIFY"*. That would explain the
`counter` failure, but it **contradicts** the `flag` result in the same hook —
under a blanket "cannot modify" rule `expect(flag).to_equal(true)` should have
failed too, and it passed.

So the discriminator is not "captured write" but something narrower. The
candidate that fits both rows is: **a write whose right-hand side reads the
captured variable is dropped, while a write of a constant is not.** That is the
same shape as the already-known
`.claude/memory/reference_stale_deployed_binary_fakes_open_defect_status.md`
finding that `x op= v` discarded the operator.

Against that, `testing_framework_spec.spl` fails on a *constant* write
(`cleanup_flag = true`), which the probe says should work. So there is a second
variable in play — nesting depth, hook count, or the surrounding `context`
block. Pinning that difference is step one of the fix; do not assume the
compound-assignment story covers both until it is measured.

## Why not fixed now

The mechanism is not yet identified, and the two observations are mutually
inconsistent under every single-sentence explanation tried above. Fixing hook
variable capture in the spec runtime without first knowing which of the two
paths (constant vs. self-referencing write, and whatever distinguishes the
in-repo case from the probe) is actually broken would be guesswork in shared
code that every spec in the repo runs through.

Next step for whoever picks this up: bisect the difference between the probe
(constant write propagates) and `testing_framework_spec.spl:138` (constant write
does not) by varying nesting and hook count one factor at a time.

**Do not "fix" the spec** by deleting the `after_each` assertion — verifying
that `after_each` actually runs is the entire point of that example.
