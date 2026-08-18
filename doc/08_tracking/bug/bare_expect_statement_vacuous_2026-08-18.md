# INVALIDATED CLAIM: bare `expect <bool-expr>` is NOT a silent no-op

- Date: 2026-08-18
- Status: **NOT A BUG** (claim disproven by direct execution). Filed as a
  negative result so the claim is not re-raised.
- Reporter claim under investigation: in
  `test/perf/ui_access/ui_access_hot_paths_spec.spl`, the statement
  `expect elapsed_ms < hard_ms` did not fail despite `elapsed_ms = 135449`
  and `hard_ms = 2000`, and the file reported `Results: 3 total, 3 passed, 0 failed`.

## Verdict

**NO.** The bare `expect <boolean-expression>` statement form is a real,
fully-wired assertion. It fails the example when the expression is false, in
every shape tested: inline in an `it` block, inside a plain top-level helper
`fn` called from an example, and under an `it`-forwarding wrapper (`slow_it`).
Zero assertions in `test/` are vacuous on account of this form.

## Proof (verbatim runner output)

Binary: `bin/simple` -> `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple` (shared Rust seed).

### Probe A — the bare form itself (`test/temp_bare_expect/probe_a_spec.spl`, not committed)

Body: `expect false`; `expect 1 == 2`; and the exact perf-spec shape
`val elapsed_ms = 135449; val hard_ms = 2000; expect elapsed_ms < hard_ms`.

```
  ✗ bare expect false
  ✗ bare expect 1 == 2
  ✗ bare expect comparison like perf spec
SPEC FILE VERDICT: test/temp_bare_expect/probe_a_spec.spl outcome=OK declared>=3 executed=3 passed=0 failed=3 skipped=0 dropped=0
spec failure: 3 of 3 example(s) failed (exit 1)
error: test-runner: spec failed
Results: 3 total, 0 passed, 3 failed
```

All three failed. The third is the literal statement and literal values from
the report — it fails.

### Probe B — matcher-form control (`probe_b_spec.spl`)

Body: `expect(false).to_be_true()`.

```
  ✗ matcher form must fail
SPEC FILE VERDICT: test/temp_bare_expect/probe_b_spec.spl outcome=OK declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0
Results: 1 total, 0 passed, 1 failed
```

Control behaves as expected; the bare form is not weaker than it.

### Probe C — the perf spec's exact indirection (`probe_c_spec.spl`)

Reproduces the two structural features the perf spec has and probe A did not:
the assertion lives in a plain top-level `fn _check_budget(...)`, and examples
are declared through a wrapper `fn slow_it(name, block): it(name, block)`.

```
  ✗ bare expect inside a plain helper fn
  ✗ matcher expect inside a plain helper fn
  ✗ bare expect via slow_it wrapper, inline
  ✗ bare expect via slow_it wrapper, in helper
SPEC FILE VERDICT: test/temp_bare_expect/probe_c_spec.spl outcome=OK declared>=4 executed=4 passed=0 failed=4 skipped=0 dropped=0
Results: 4 total, 0 passed, 4 failed
```

Neither the helper-fn indirection nor the `it`-wrapper suppresses the failure.

## Mechanism — why the bare form works

`src/lib/nogc_sync_mut/spec.spl`:

```
pub fn expect(value: bool) -> i64:
    if not value:
        fail_assertion("Expected true, got false")
    _stable_expect_helper(value, false, not value)
```

The `bool` overload asserts EAGERLY: it records the failure the moment
`expect` is called, before any matcher could be chained. Because
`fail_assertion` is just

```
pub fn fail_assertion(message: text):
    current_test_errors.push(message)
```

— a push onto a module-level global — it works from any call depth, which is
why the helper-fn and wrapper shapes in probe C all fail correctly.

If a matcher IS chained afterwards, the eagerly-pushed error is popped back
off by `_expect_begin_matcher`, which every matcher calls first
(`spec.spl:715`):

```
fn _expect_begin_matcher(implicit_error: bool):
    if implicit_error and current_test_errors.len() > 0:
        val _ = current_test_errors.pop()
```

So `expect(x)` alone is a hard assertion, and `expect(x).to_equal(y)` retracts
the provisional error and re-decides. A non-bool subject with no matcher is
also NOT silent — the generic overload pushes an explicit diagnostic
(`spec.spl:701-708`):

```
pub fn expect(value) -> i64:
    fail_assertion("vacuous expect: expect(...) was never consumed by a matcher — chain .to_equal(...)/.to_contain(...) or use assert_true(...)")
```

The vacuous-expect hazard this bug was filed against is therefore already
designed for and already guarded, in both directions.

## Actual explanation of the reported perf-spec observation

`_bench_request` returns **microseconds**, not milliseconds:

```
val elapsed = rt_time_now_unix_micros() - start
print "[perf] {label}: {elapsed} us for {iterations} iterations (avg={avg} us/iter)"
elapsed
```

and `_check_budget` converts before comparing:

```
fn _check_budget(label: text, elapsed_us: i64, soft_ms: i64, hard_ms: i64):
    val elapsed_ms = elapsed_us / 1000
```

The reported `135449` is the printed `[perf] ... us` figure, i.e. 135 ms, not
135449 ms. `135 < 2000` is true, so the assertion passed **correctly**. The
report misread the unit; there is no missed failure.

## Census of the bare form in `test/`

Exhaustive scan (`/usr/bin/grep -rE '^[[:space:]]*expect[[:space:]]+[^(]' --include=*.spl test/`):

| shape | count |
|---|---|
| bare `expect <expr>` statements, total | 27,239 |
| ...of which carry a comparison/logical operator (`==`, `!=`, `<`, `>`, `and`, `or`, `in`) | 16,457 |
| ...of which use the `expect X to_<matcher> Y` infix shape | 5,011 |

Top files by occurrence:

```
test/01_unit/lib/skia/shaper_spec.spl:206
test/unit/app/tooling/command_dispatch_spec.spl:163
test/01_unit/app/tooling/command_dispatch_spec.spl:160
test/03_system/feature/app/easy_fix_rules_spec.spl:140
test/unit/lib/std/json_spec.spl:138
test/01_unit/lib/std/json_spec.spl:138
test/unit/app/ui/widget_panel_text_divider_spec.spl:123
test/01_unit/app/ui/widget_panel_text_divider_spec.spl:123
test/unit/app/tooling/url_utils_spec.spl:120
test/01_unit/app/tooling/url_utils_spec.spl:120
test/unit/compiler/parser/error_recovery_intensive_spec.spl:114
test/01_unit/compiler/parser/error_recovery_intensive_spec.spl:114
test/unit/std/dashboard_spec.spl:113
test/unit/lib/common/dashboard_spec.spl:113
test/01_unit/std/dashboard_spec.spl:113
```

**The vacuous-assertion count attributable to this form is 0.** The bare form
is the dominant assertion idiom in this repo (27k sites) and it is load-bearing,
not decorative. Had it been a no-op, essentially the entire suite would have
been vacuous — which is itself a reason the original claim deserved this level
of disproof rather than a code read.

## Residual item (separate, real, NOT this bug)

The perf spec does not currently run at all in the perf shard. From a full
perf-shard log in this lane's scratchpad:

```
SPEC FILE VERDICT: test/perf/ui_access/ui_access_hot_paths_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module
```

`reason=unresolved-module` — the file is dropped before any example executes.
That is a genuine defect in its own right (a perf budget that never runs), and
it is orthogonal to `expect` semantics. It should be tracked separately.

## Pinning spec

No new spec is committed. A spec pinning "bare `expect false` fails" would be
GREEN today (probes A/B/C already demonstrate it) and would duplicate coverage
that the framework's own behaviour already provides at 27,239 call sites; the
probe files used here were scratch and are not part of the suite. Nothing needs
the runner fixed, so there is no failing spec to withhold.

## Fix required

**None.** No change to the runner, the spec library, or the Rust seed. The
one action item is documentation: the reporter's confusion came from the
`[perf] ... us` print being read as milliseconds. Worth considering (not filed
as a blocking change) is making `_bench_request`'s print state both units, or
naming the parameter `elapsed_us` at the call site.
