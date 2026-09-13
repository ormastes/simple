# BUG: a write inside `after_each` that reads the captured variable is lost; a constant write is not

## Triage 2026-09-13 — narrowed: the in-repo case is now fixed, the probe case still reproduces

Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (interpreter mode).

- **In-repo case FIXED.** `test/01_unit/std/feature_validation/testing_framework_spec.spl`
  "Feature #184 - After Each Hooks" (now lines 160-178) declares
  `cleanup_flag` at MODULE level (not inside the `describe` block) and both
  examples now PASS: `SPEC FILE VERDICT: ... outcome=OK declared>=47
  executed=47 passed=47 failed=0`. This is the same class this session
  independently confirmed fixed in
  `spec_harness_module_global_mutation_via_function_invisible_2026-08-07.md`
  — module-level `var` mutation performed inside a called function (here, the
  `after_each` hook) is now visible.
- **Probe case STILL REPRODUCES.** Re-ran this doc's own probe (`describe`
  block-scoped `var counter = 0`, captured by `after_each`, mutated with the
  self-referencing `counter = counter + 1`) verbatim:
  `expected 0 to equal 1` — identical to the original 2026-08-04 report. So
  the discriminator is confirmed to be **declaration scope** (module-level
  `var` vs. `describe`-block-scoped captured `var`), not constant-vs-
  self-referencing-write as originally guessed — the `flag = true` /
  `cleanup_flag = true` constant-write case now passes in BOTH scopes; only
  `describe`-scoped closure-captured vars still lose a write on the path back
  out of the hook, and only(as far as tested) for a self-referencing RHS.
- **Not fixed here.** This is closure/capture write-back semantics in the
  interpreter's `describe`/`it`/hook dispatch (not `src/lib/nogc_sync_mut/spec.spl`
  alone — the capture mechanism is interpreter-level, matching
  `.claude/rules/language.md`'s documented Runtime Limitation "Nested closure
  capture - can READ outer vars, CANNOT MODIFY"). Fixing it correctly needs
  the interpreter's closure environment model, which is a bigger and riskier
  change than this lane's budget; left OPEN, repro re-confirmed and narrowed
  above for whoever picks it up next.

**Status:** OPEN (narrowed 2026-09-13 — module-level case fixed, describe-scope case remains)
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

## Triage 2026-09-13

The doc's own recommended next step is a careful bisection (constant vs. self-referencing write, nesting, hook count) of shared spec-harness capture semantics that every spec in the repo runs through -- high blast-radius, not appropriate to guess at within a single-bug budget. Leaving OPEN, no code change made; did not weaken the `after_each` assertion.
