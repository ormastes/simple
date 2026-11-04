# async_spec: destructured Future from anon-tuple Promise.new() gives inconsistent poll() results

## 2026-11-03 current-source triage: production behavior unverified

The historical spec description below is no longer the current test source.
`test/01_unit/lib/std/async_spec.spl` now declares `enum TaskState` and its
local Future/Promise doubles use module-registry `state_id` handles. Those
doubles no longer exercise the original embedded-state anonymous-tuple shape;
their success cannot establish production `std.nogc_async_mut.async` behavior.
The inventory's `async/task.spl` location is not evidence of a task-owner bug.

Added `test/01_unit/lib/nogc_async_mut/async_promise_pair_persistence_spec.spl`
imports the production Promise and Poll owners. It checks pending-to-ready
completion followed by repeated polls, independent destructured pairs, and
rejected second completion preserving the original payload. Current Poll's
public payload helper is `poll_unwrap`; the removed `.unwrap()` method is not
reintroduced merely to reproduce stale syntax.

Execution is **TEST_BLOCKED**: no admitted pure-Simple test runtime is available
on this Windows host. The tracked `bin/simple.exe` is a Rust seed and was not
used as a substitute. No failure reproduction, repair, or PASS is claimed;
this record remains OPEN. Resume once an admitted full CLI exists:
`<qualified-selfhosted-runtime> test test/01_unit/lib/nogc_async_mut/async_promise_pair_persistence_spec.spl --mode=interpreter`.
Record producer/source/backend/runtime hashes and actual scenario counts.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Canonical database reconciliation — 2026-11-03

OPEN; PR #6301 MERGED at 5cec7885187661e950f941045cdb6b8d522a4884 and contributes production-owner Promise/Future detectors only, not a production repair. TEST_BLOCKED: real anonymous-tuple readiness/value/second-completion scenarios UNRUN without a qualified self-hosted runtime. Await detector execution and triage; historical surrogate-spec repairs are not production-state proof.

## 2026-11-04 triage (libbug-async): INTERPRETER-ROOT, lib is correct
`async_promise_pair_spec.spl` under Rust-seed `run`: 0/4 pass. Not tuple-related and not Promise/Future: a class instance stored in another class's field is value-copied by the seed tree-walk interpreter when the entry is not `main` (JIT path under `fn main` aliases correctly). Lib-free repro: `class Fu: n:i64; me set(v)`, `class Pr: fu: Fu; fn complete(v): self.fu.set(v)`; `val f = Fu(n: 0); val p = Pr(fu: f); p.complete(42); print f.n` called from a non-`main` function prints 0 (expected 42); same code under `fn main` prints 42. No lib change made.
