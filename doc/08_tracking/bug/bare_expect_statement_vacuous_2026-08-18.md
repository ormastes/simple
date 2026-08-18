# A matcher-form `expect(...)` silently swallows genuine assertion failures in the same example

- Date: 2026-08-18
- Status: **CONFIRMED BUG, OPEN.** Fail-open assertion loss. Not fixed here.
- Severity: HIGH — green tests that assert nothing.
- Component: `src/lib/nogc_sync_mut/spec.spl` (pure Simple stdlib — **not** the
  Rust seed; no bootstrap needed to fix).
- Found via: `test/perf/ui_access/ui_access_hot_paths_spec.spl` reporting
  `3 passed` while a 106,627 ms measurement blew a 2,000 ms budget.

> **Correction notice.** An earlier revision of this file (commit `14ccb6a20c8`)
> concluded "NOT A BUG" from probes that did not reproduce the real spec's
> shape, and attributed the report to a microsecond/millisecond misreading.
> **That conclusion was wrong and is retracted.** The perf spec was
> subsequently run to completion and blew its budget by 53x while still
> reporting all examples passed. The retracted reasoning is preserved in
> "Retracted hypothesis" below so the mistake is not repeated.

## The bug in one sentence

If an example calls the matcher form `expect(x).to_...()` **anywhere**, then a
failing bare `expect <bool-expr>` in that same example is silently discarded and
the example reports PASS.

## Trigger conditions (established by bisection)

| example contains | failing assertion honoured? |
|---|---|
| bare `expect` only (one or many) | YES — correct |
| matcher `expect(x).to_…()` only (any mix of pass/fail, any order) | YES — correct |
| **matcher form AND bare form, in either order** | **NO — failure discarded** |

Both orders lose the failure: a bare failure *before* the matcher is retroactively
erased, and a bare failure *after* the matcher never registers. Two consecutive
bare failures after one matcher are both lost.

## Proof (verbatim runner output)

Binary: `bin/simple` -> `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple` (shared Rust seed).

### The originating case — real spec, real numbers

`bin/simple test test/perf/ui_access/ui_access_hot_paths_spec.spl`:

```
[perf] ui_access snapshot route: 106627227 us for 100 iterations (avg=1066272 us/iter)
[perf] Warning: ui_access snapshot route took 106627ms (target: <100ms)
[perf] ui_access query route: 78003694 us for 100 iterations (avg=780036 us/iter)
[perf] Warning: ui_access query route took 78003ms (target: <100ms)
[perf] ui_access ensure-style state route: 79377350 us for 100 iterations (avg=793773 us/iter)
[perf] Warning: ui_access ensure-style state route took 79377ms (target: <100ms)
SPEC FILE VERDICT: test/perf/ui_access/ui_access_hot_paths_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0
Results: 3 total, 3 passed, 0 failed
```

`elapsed_ms = 106627`, `hard_ms = 2000` — the spec's own warning line prints the
millisecond value, so there is no unit ambiguity. `expect elapsed_ms < hard_ms`
is false by 53x and the example still passed. Each of these three examples calls
`expect(preflight.0).to_equal(200)` before reaching `_check_budget`.

### Minimal bisection — probe F (`test/tmp_probe_e/probe_f_spec.spl`, scratch, not committed)

Every example asserts something false; every one is marked `MUST FAIL`.
F1–F4 have a preceding matcher call, F5 does not. Nothing else differs.

```
  ✓ F1 one to_equal then bare expect -- MUST FAIL
  ✓ F2 to_contain then bare expect -- MUST FAIL
  ✓ F3 three matchers (perf-spec shape) then bare expect -- MUST FAIL
  ✓ F4 matcher then inline bare expect -- MUST FAIL
  ✗ F5 no preceding matcher, control -- MUST FAIL
SPEC FILE VERDICT: test/tmp_probe_e/probe_f_spec.spl outcome=OK declared>=5 executed=5 passed=4 failed=1 skipped=0 dropped=0
Results: 5 total, 4 passed, 1 failed
```

A ✓ here is the bug: four false assertions reported as passing. F5 is the
control that proves the bare form works on its own.

### Characterisation — probe G

```
  ✓ G1 matcher then TWO failing bare expects -- MUST FAIL
  ✗ G2 passing bare expect then failing bare expect -- MUST FAIL
  ✓ G3 failing bare expect FIRST, then a passing matcher -- MUST FAIL
  ✓ G4 bool-subject matcher then failing bare expect -- MUST FAIL
  ✗ G5 control: single failing bare expect -- MUST FAIL
Results: 5 total, 3 passed, 2 failed
```

G3 is the worst shape: the failure is recorded **first** and a later, entirely
unrelated *passing* matcher erases it. G1 shows more than one failure can be
lost. G2/G5 confirm bare-only examples are sound.

### Bound on blast radius — probe H (matcher-only examples)

```
  ✗ H1 failing matcher then PASSING matcher -- MUST FAIL
  ✗ H2 control: single failing matcher -- MUST FAIL
  ✗ H3 two failing matchers -- MUST FAIL
  ✗ H4 passing to_be_true then failing to_be_true -- MUST FAIL
  ✗ H5 failing to_be_true then passing to_be_true -- MUST FAIL
Results: 5 total, 0 passed, 5 failed
```

All correct. **Matcher-only examples are not affected**, which is what keeps
this from implicating the whole suite.

### Infix matcher form is sound — probe I

The repo also uses an infix shape, `expect X to_contain Y` (5,011 sites). It
behaves correctly on its own:

```
  ✗ I1 infix to_contain, substring ABSENT -- MUST FAIL
  ✗ I2 infix to_equal, wrong value -- MUST FAIL
  ✓ I3 infix to_contain, substring PRESENT -- must pass
  ✗ I4 control: bare expect false -- MUST FAIL
SPEC FILE VERDICT: test/tmp_probe_i/.spipe_matchers_922178_1787047304062025_probe_i_spec.spl outcome=OK declared>=4 executed=4 passed=1 failed=3 skipped=0 dropped=0
Results: 4 total, 1 passed, 3 failed
```

**But note the rewritten filename in the verdict** — `.spipe_matchers_…`. The
infix form is DESUGARED into matcher-form calls by a preprocessor before
execution. It therefore **arms the swallow exactly like a literal
`expect(x).to_…()` does**, and any census that greps only for the literal
parenthesised form undercounts the at-risk set. The table below accounts for
this.

### Non-triggers ruled out (probes A, C, E)

Bare `expect false`, `expect 1 == 2`, `expect elapsed_ms < hard_ms`, the same
inside a plain top-level helper `fn`, under an `it`-forwarding wrapper
(`slow_it`), with the division `elapsed_us / 1000`, with a preceding
`if`/`print`, with literal or runtime-derived operands — all fail correctly when
no matcher form is present. Probe E ran the perf spec's `_check_budget` verbatim
across five variants: `Results: 5 total, 0 passed, 5 failed`.

## Mechanism

`src/lib/nogc_sync_mut/spec.spl`. Failures are recorded by appending to a
module-level list:

```
pub fn fail_assertion(message: text):
    current_test_errors.push(message)
```

The bare form asserts eagerly and correctly:

```
pub fn expect(value: bool) -> i64:
    if not value:
        fail_assertion("Expected true, got false")
    _stable_expect_helper(value, false, not value)
```

The non-bool form pushes a provisional error so that an unconsumed `expect(x)`
cannot be silent:

```
pub fn expect(value) -> i64:
    fail_assertion("vacuous expect: expect(...) was never consumed by a matcher — chain .to_equal(...)/.to_contain(...) or use assert_true(...)")
    _stable_expect_helper(value, false, true)
```

Every matcher then retracts that provisional error before deciding
(`spec.spl:715`) — and this is the defect:

```
fn _expect_begin_matcher(implicit_error: bool):
    if implicit_error and current_test_errors.len() > 0:
        val _ = current_test_errors.pop()
```

Two compounding faults:

1. **The retraction is an untargeted LIFO `pop()`.** It removes *the most recent
   error in the list*, with no check that the popped entry is the provisional
   one this `expect` pushed. Any genuine failure sitting on top is destroyed
   instead. This is what G3 shows.
2. **`implicit_error` is read from a single mutable global that is never reset
   per example.** `_expect_helper_slots` holds one `ExpectHelper` reused and
   mutated in place by `_stable_expect_helper`; every `expect(...)` overwrites
   `helper.implicit_error`. Once any call leaves it `true`, later matcher
   invocations keep popping. Combined with the bare form's own
   `implicit_error = not value` (i.e. `true` exactly when the assertion FAILED),
   a failing bare `expect` arms the very flag that authorises the next pop.

The `pop()` is guarded only by `current_test_errors.len() > 0`, so it cannot
detect that it is discarding someone else's failure. The design comment at
`spec.spl:640-648` notes that an "arm early, auto-check at the end" scheme was
already tried and rejected for being fail-open; this pop is the same fail-open
hazard in a different place.

## Census — blast radius

Exhaustive scan with `/usr/bin/grep` over `test/`:

| measure | count |
|---|---|
| `*_spec.spl` files | 20,550 |
| files that ARM the bug (literal `expect(x).to_…` **or** infix `expect X to_… Y`, which desugars to it) | 18,942 |
| files using the plain bare form `expect <expr>` (infix excluded) | 931 |
| **files with BOTH — at risk** | **71** |
| bare `expect` statement sites (all `.spl` under `test/`) | 27,239 |
| ...with a comparison/logical operator | 16,457 |
| ...in the infix `expect X to_… Y` shape (arms, does not trigger) | 5,011 |

Top at-risk files by plain-bare-`expect` count:

```
48 test/unit/std/collections_spec.spl
48 test/01_unit/std/collections_spec.spl
46 test/03_system/feature/language/placeholder_lambda_spec.spl
42 test/01_unit/os/userlib/process_spawn_path_spec.spl
37 test/feature/usage/parser_syntax_validation_spec.spl
37 test/03_system/feature/usage/parser_syntax_validation_spec.spl
36 test/feature/usage/parser_error_recovery_spec.spl
36 test/03_system/feature/usage/parser_error_recovery_spec.spl
33 test/unit/lib/database/database_stats_spec.spl
33 test/01_unit/lib/database/database_stats_spec.spl
30 test/unit/app/tooling/algorithm_utils_spec.spl
30 test/01_unit/app/tooling/algorithm_utils_spec.spl
29 test/shared/types/union_impl_spec.spl
29 test/feature/usage/treesitter_parser_spec.spl
29 test/03_system/feature/usage/treesitter_parser_spec.spl
```

**71 files can currently contain vacuous assertions.** That is a file-level
upper bound: the trigger is per-EXAMPLE, so a file counted here is only actually
affected where both forms appear inside the same `it`. It is not a lower bound
either — one such file can hide many lost assertions (G1: two in one example).

The 27,239 bare sites are NOT all vacuous. The bare form is the repo's dominant
assertion idiom and is sound on its own; only its co-occurrence with the matcher
form inside one example is dangerous.

Confirmed affected: `test/perf/ui_access/ui_access_hot_paths_spec.spl` — three
perf budgets, all vacuous, currently reporting green while running 39x-53x over
budget. Enumerate the rest with:

```sh
/usr/bin/grep -rlE '^[[:space:]]*expect\(.*\)\.to_|^[[:space:]]*expect[[:space:]]+.*[[:space:]]to_' \
  --include=*_spec.spl test/ | sort -u > /tmp/armers.txt
/usr/bin/grep -rE '^[[:space:]]*expect[[:space:]]+[^(]' --include=*_spec.spl test/ \
  | /usr/bin/grep -vE '[[:space:]]to_' | cut -d: -f1 | sort -u > /tmp/bareplain.txt
comm -12 /tmp/armers.txt /tmp/bareplain.txt
```

## Proposed fix

The fix is in pure Simple (`src/lib/nogc_sync_mut/spec.spl`); the Rust seed is
not involved, and per `.claude/rules/commands.md` a `src/lib/**` edit needs no
build. Preferred option 1, in order:

1. **Make the retraction targeted instead of LIFO.** Have the provisional push
   return its index (or a token), store it on the `ExpectHelper`, and have
   `_expect_begin_matcher` remove *that specific entry*, and only if it is still
   the entry it pushed. A pop that cannot identify what it is removing must not
   remove anything. This alone fixes G3 and F1–F4.
2. **Reset the expectation state per example.** Clear `_expect_helper_slots`
   (or at minimum `implicit_error`) at the start of each `it`, so a stale `true`
   from a previous statement or example cannot authorise a pop. Note the
   documented constraint at `spec.spl:640-648` that module-level spec state does
   not persist across examples under this runner — the reset therefore belongs
   in the per-example entry path, not a file-level hook.
3. **Fail closed if a retraction would remove a non-provisional error.** Rather
   than dropping it, record a framework-level failure ("assertion bookkeeping
   lost a real failure"). A test framework must never silently reduce the
   failure count.

Additionally, and independent of the fix, a lint should reject mixing the two
`expect` forms within one example until the runtime fix lands, since that is the
exact trigger and it is statically detectable.

## Pinning spec — NOT committed, deliberately

A spec pinning the correct behaviour was written and proven to reproduce
(probe F above), but it **fails on today's runner** and would land the tree red,
so it is not committed per instruction. Commit it together with the fix. It is
exactly probe F/G: examples that each contain one matcher-form `expect` and one
failing bare `expect`, asserted to FAIL. Suggested home:
`test/01_unit/lib/std/spec_expect_failure_retention_spec.spl`. Until the runner
is fixed, that spec cannot be green, and no existing test was skipped, weakened,
or deleted in the course of this investigation.

## Retracted hypothesis (for the record)

The first revision argued the report was a microsecond/millisecond misreading:
`_bench_request` does return microseconds and `_check_budget` does divide by
1000. That is all true and still irrelevant — the spec's own
`[perf] Warning: ... took 106627ms` line prints the already-converted value, and
`106627 < 2000` is false. The error was concluding from probes (A/C) that shared
the helper-fn and wrapper shape but omitted the preceding matcher call, and
treating "the mechanism reads correct in source" as evidence. The lesson: the
bisection must vary one thing at a time against the REAL failing artifact, and a
"not a bug" verdict needs the original artifact reproduced green-to-red, not
just a lookalike.

## Related, separate

Under the full perf shard the same file is dropped before execution:

```
SPEC FILE VERDICT: test/perf/ui_access/ui_access_hot_paths_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module
```

`reason=unresolved-module` in the shard, but it runs standalone. Different
defect, needs its own record.

## ROOT CAUSE FOUND (2026-08-18, lane-test-fix) — it is the RUST SEED, not spec.spl

The "Mechanism" section above is wrong about WHERE the loss happens for
`bin/simple test`. Verified by instrumenting `src/lib/nogc_sync_mut/spec.spl`
with prints and observing NONE of them fire: `describe`/`it`/`expect` in a spec
run by `bin/simple test` are intercepted by interpreter BUILTINS in the Rust
seed (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`), so
`_expect_begin_matcher` at spec.spl:715 is not on that path at all. (That LIFO
pop is still a latent fail-open in the pure-Simple runner and was fixed too.)

The real mechanism, in the seed:

- A failing bare `expect <cond>` sets only `BDD_EXPECT_PROVISIONAL`
  (`bdd.rs`, three sites), never the hard `BDD_EXPECT_FAILED`.
- Any `.to_*()` matcher clears `BDD_EXPECT_PROVISIONAL` unconditionally and
  sets `BDD_MATCHER_RAN` (`interpreter_method/mod.rs:371-375`).
- At example end (`bdd.rs:862`) the verdict was
  `hard_failed || (provisional && !matcher_ran) || vacuous`.

`BDD_MATCHER_RAN` is MONOTONIC per example, so one matcher anywhere suppressed
a standing provisional raised by an unrelated bare `expect` — in either order.
That is exactly the observed table.

### Fix applied

Targeted retraction by ordinal, mirroring option 1 of "Proposed fix":

- New thread-locals `BDD_EXPECT_SEQ` (ordinal of the most recent `expect(...)`
  in this example) and `BDD_PROVISIONAL_SEQ` (ordinal of the expect that raised
  the standing provisional), reset at example start and in `clear_bdd_state()`.
- A matcher retracts the provisional ONLY when `BDD_PROVISIONAL_SEQ ==
  BDD_EXPECT_SEQ`, i.e. it is chained to the very expect that raised it.
- Example-end verdict becomes `hard_failed || provisional || vacuous`;
  `BDD_MATCHER_RAN` is kept for diagnostics but is no longer load-bearing.
- `src/lib/nogc_sync_mut/spec.spl`: the blind `current_test_errors.pop()` is
  now gated on `_expect_provisional_len` matching the current list length, so
  it can only remove the entry that this expect pushed.

### Reproducing fixture

`test/fixture/spec/expect_failure_retention_fixture.spl` (deliberately RED,
deliberately NOT named `*_spec.spl` so directory sweeps do not collect it).
7 examples: 6 must FAIL, 1 positive control must pass.

```sh
bin/simple test test/fixture/spec/expect_failure_retention_fixture.spl --no-cover-check
# BUGGY seed  : Results: 7 total, 4 passed, 3 failed   <- 3 real failures lost
# FIXED seed  : Results: 7 total, 1 passed, 6 failed
```

Verbatim RED, measured against the shared seed
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`:

```
  ✓ bare expect after a passing matcher MUST FAIL
  ✓ bare expect before a passing matcher MUST FAIL
  ✓ two bare expects after a matcher MUST FAIL
  ✗ failing matcher only MUST FAIL
  ✗ failing matcher then passing matcher MUST FAIL
  ✗ bare expect only MUST FAIL
  ✓ control all assertions pass MUST PASS
Results: 7 total, 4 passed, 3 failed
```

### GREEN is BLOCKED — not verified

The fix cannot be exercised in this lane: the Rust seed at HEAD does not
compile, for two defects unrelated to this change, so no fixed binary can be
built and `bin/simple` (a shared seed, not to be replaced) still carries the
bug:

```
error[E0432]: unresolved import `crate::interpreter::module_globals_generation`
  --> compiler/src/interpreter_call/core/function_exec.rs:10
error[E0599]: the method `as_ref` exists for reference `&simple_parser::FunctionDef` ...
  --> compiler/src/interpreter_sffi.rs:125
```

`module_globals_generation` is defined NOWHERE in the tree. Until those are
fixed and a seed is rebuilt, this fix is UNVERIFIED and the bug stays OPEN.
A pure-Simple pinning spec is not possible either: the failure bookkeeping is
interpreter thread-local state that an example cannot read from inside itself
(two designs tried and discarded — an exported drain helper in spec.spl reads a
stale module env and always returns 0; a child-process spec produced no output
under the runner). The fixture above is the pin until the seed builds.
