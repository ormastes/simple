# async_spec: destructured Future from anon-tuple Promise.new() gives inconsistent poll() results

**Status:** open
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** interpreter / anonymous-tuple destructuring (likely same landmine class as
`resource_handle_anon_tuple_field_access_2026-07-20.md`)

## Note: a separate stale-syntax issue exists in this same file (NOT applied — see below)

`test/01_unit/lib/std/async_spec.spl` currently has 19 failures of the form
`semantic: method 'Pending' not found on type 'TaskState'`, because the
inline test double is declared `class TaskState:` with bare variant-name
lines (`Pending`/`Running`/...) instead of `enum TaskState:` (confirmed
against the working convention in `src/lib/common/target.spl`'s
`enum TargetArch:`). Applying that one fix (`class` -> `enum`,
value-preserving) is straightforward and verified to clear all 19 "method
not found" failures — **but the spec still does not go green afterward**:
one genuine failure remains (documented below), plus a run that stops
early partway through the `Executor` describe block without completing the
remaining ~5 describe blocks in the file (see "Secondary symptom" below).
Since the spec can't be brought to a verified `PASS` either way, this
campaign's rule is to leave the spec file unmodified and document the
findings rather than carry a partial edit — **the `class`/`enum` edit was
NOT kept in the file**; do the `class` -> `enum` migration first when
someone follows up on the failure below.

## Symptom

```
Promise<T>
  ✓ should create promise-future pair
  ✓ should complete promise
  ✓ should not complete twice
  ✗ should make future ready after completion
    semantic: panic: Poll is pending
```

Test body:

```
it "should make future ready after completion":
    val (future, promise) = Promise.new()
    expect(future.is_ready()).to_equal(false)
    expect(promise.complete(33)).to_equal(true)
    expect(future.is_ready()).to_equal(true)     # <- PASSES
    expect(future.poll().unwrap()).to_equal(33)  # <- PANICS: "Poll is pending"
```

`future.is_ready()` is defined as `self.poll().is_ready()` (same underlying
`poll()` call). So `future.is_ready()` returning `true` means
`future.poll()` returned `Poll(ready: true, ...)` on that call — yet the
very next statement's direct `future.poll()` call returns
`Poll(ready: false, ...)` (pending), with no intervening mutation between
the two calls on the same `future` value.

## Root-cause hypothesis

`Promise.new()` returns an **anonymous tuple** `(Future, Promise)`:

```
static fn new() -> (Future, Promise):
    var state = AsyncState(ready: false, value: 0)
    (Future(state: state), Promise(state: state))
```

and the caller destructures it: `val (future, promise) = Promise.new()`.
Both `Future` and `Promise` embed the *same* `state` object so that
`promise.complete()` mutating `state.ready`/`state.value` should be visible
through `future.poll()` too. The inconsistency between two back-to-back
`poll()` calls on the same `future` binding (one via `is_ready()`, one
direct) strongly suggests the destructured `future` local is not a stable
reference to one consistent object — consistent with the same anonymous
-tuple-return class of defect already flagged in
`resource_handle_anon_tuple_field_access_2026-07-20.md` (there manifesting
as `.0`/`.1` positional access misbehaving; here manifesting as
destructuring-assignment producing a value whose nested-object identity
doesn't stay stable across method calls).

## Secondary symptom (only observed with the `class`->`enum` fix applied)

With the `TaskState` `class`->`enum` fix from above applied locally (not
committed — see note at top), re-running the file (twice, deterministically)
stops partway through the `Executor` describe block (`should spawn multiple
tasks` is the last example that prints, no closing `N examples, M failures`
line for that block, and none of the ~5 remaining describe blocks execute).
Final summary: `Passed: 17, Failed: 1`, well under the 90s timeout
(~62-65s elapsed). Notably, the *pristine* (current, unedited) file does
NOT show this early-stop — it runs all 9 describe blocks to completion
(just with many more failures, from the `TaskState` class/enum issue on
top of this one). So the early-stop only manifests once the `TaskState`
issue is fixed and execution reaches further into the file; flagging so a
future fix attempt isn't confused by it appearing only after that
first fix lands.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/std/async_spec.spl --no-session-daemon
```

Against the current (pristine, unedited) file this reproduces both this
doc's "Poll is pending" failures AND the unrelated 19 `TaskState`
`class`/`enum` failures together (30 examples, ~13 failures across several
describe blocks) — the "Symptom" block above isolates just the
`Poll is pending` case by describing output with the `TaskState` fix
applied locally for clarity; that fix is not present in the committed file.

## Affected specs seen this shard

- `test/01_unit/lib/std/async_spec.spl` — 2 stacked issues: (1) `TaskState`
  declared `class` instead of `enum` (straightforward value-preserving fix,
  not applied to the file — see top note), and (2) this doc's genuine
  `Future.poll()` inconsistency, which still blocks full green even after
  fix (1) is applied.
