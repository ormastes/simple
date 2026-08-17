# BUG: a write inside `after_each` that reads the captured variable is lost; a constant write is not

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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
