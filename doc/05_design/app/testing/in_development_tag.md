# `@tag:in-development` — work-in-progress tests that are expected to fail

**Date:** 2026-08-23
**Status:** Implemented
**Owner files:** `src/lib/nogc_sync_mut/spec/in_development.spl`,
`src/app/test_runner_new/test_runner_main.spl`,
`src/app/test_runner_new/test_runner_single.spl`
**Specs:** `test/01_unit/lib/spec/in_development_tag_spec.spl`,
`test/02_integration/test_runner/in_development_tag_runner_spec.spl`

## Problem

A test being written for code that does not work yet has, today, only two
homes: land it red and redden the whole suite for everyone, or don't land it
at all. Both are bad. The first makes the suite verdict useless as a signal;
the second means the test is written twice, or never.

There is a third bad option that must be explicitly ruled out: comment it
out, or `skip()` it. That makes the debt *invisible*, and invisible debt is
how a "temporary" WIP test becomes a permanently dead file nobody remembers.

## Tag name

`# @tag:in-development`.

### Why reuse `@tag:`

`@tag:<name>` is already the only tag channel in this tree. Census
2026-08-23 over `src/` + `test/`: **57 distinct names, 1022 occurrences**
(`api` 183, `stdlib` 171, `system` 198, `gpu` 73, `simd` 26, ...). Building
a second annotation scheme next to it would have been the "parallel scheme"
the request explicitly forbids.

The `SkipCondition.tags: [text]` field in `condition.spl:43` was surveyed and
deliberately NOT extended. It is **dead**: there is no `matches_tags`
function, `tags` is stored by `create_skip_condition` and read by nothing.
Reviving a dead field as the carrier for a live feature would have made the
feature depend on machinery that has never run.

### Why `in-development` and not `in_development`

The census shows multi-word tag names in this tree are **already
hyphenated**: `back-compat`, `api-individual`, `api-grouped`,
`evidence-source-contract`, `evidence-live-guest`, `linux-hosted-wm`,
`gui-smf-dynlib`. Hyphenation is the convention; underscore would have been
the deviation.

### Why not `wip`, `pending`, or `skip`

- **`pending`** — `std.spec.pending()` already means "this example is a
  placeholder that ran nothing". The runner counts it on a channel
  deliberately separate from skips (`count_real_skips`,
  `test_runner_single.spl:441`), and the zero-executed greenwash guard
  exists precisely so a file full of `pending()` cannot read as green.
  In-development is the opposite shape: the test is **written and runs**, it
  just does not pass yet.
- **`skip`** — `skip()`/`skip_it()` state that the *host* cannot run the
  test (no GPU, wrong OS). That is a claim about the environment.
  In-development is a claim about the **code under test**.
- **`wip`** — zero occurrences in the tree. Inventing an abbreviation when
  the convention is spelled-out lowercase words is a new scheme, not reuse.

## Semantics (the decisions this document exists to record)

| invocation | tagged spec FAILS | tagged spec PASSES |
|---|---|---|
| sweep (`simple test`, `simple test test/01_unit`) | neutralised: **not** a suite failure. Printed per file, totalled in the summary. | **`IN-DEVELOPMENT UNEXPECTED PASS`** — reported loudly, totalled separately, still not a suite failure |
| explicit path (`simple test path/to/x_spec.spl`) | runs, fails honestly, normal red, normal exit code | runs, passes, plus an advisory that the tag can come off |

### Decision 1: "skip" means skipped from the verdict, not from execution

The tagged file **is still run** during a sweep; only its failure is
neutralised.

The alternative — genuinely not executing it, which is what the two existing
file-level filters `is_skip_marker_file` and `path_mode_matches` do — was
rejected because **a file that is never executed can never be observed to
have started passing.** That makes "report the unexpected pass"
unimplementable, and unimplementable promotion detection means in-development
tests rot forever: exactly the failure mode this feature exists to prevent.

The cost is honest and stated: a sweep still pays the WIP test's runtime. It
buys back the promotion signal. The existing per-spec timeout already bounds
the worst case.

### Decision 2: an unexpected pass is loud, not silent

A tagged spec that passes prints

```
IN-DEVELOPMENT UNEXPECTED PASS <path> (N example(s) passed) — ready to promote: remove `# @tag:in-development`
```

It is **not** converted into a failure. Mirroring xfail-strict and failing
the suite on good news would punish the developer who just made it work, and
would create pressure to delete the tag *before* landing the fix — losing the
signal. The action is named in the line so the reader does not have to infer
it.

It is also not left as an ordinary silent pass: an in-development test that
quietly starts passing and says nothing is a test that stays tagged forever.

### Decision 3: explicit path runs honestly

Explicit targeting is detected from `TestOptions.path_explicit` +
`TestOptions.paths`, both of which **already exist** — no field was added to
`TestFileResult`/`TestOptions`, which belong to another lane.

A **directory** target is not explicit targeting of the files beneath it.
`simple test test/01_unit` is a sweep and gets sweep semantics; if a
directory counted as explicit, nearly every real invocation would go
honest-red and the whole feature would be defeated.

### Decision 4: a tagged spec that crashes or times out is still just failing

`classify_in_development` folds `timed_out` and a non-empty `error` into one
`errored` input. Without this a WIP spec that segfaults would escape the
neutralisation through the error channel and redden the suite anyway.

### Decision 5: a tagged spec that executed nothing is NOT a promotion signal

Tagged, zero passed, zero failed classifies as `ExpectedFailure`, not
`UnexpectedPass`. Otherwise an empty or unresolvable WIP file would announce
itself as ready to promote.

### Decision 6: the neutralised shape stays recoverable without a new field

`TestFileResult` belongs to a sibling lane and was not touched. A neutralised
file is left as `passed=0, failed=0, skipped=N>0`; an unexpected pass as
`passed>0, failed=0`. `in_development_totals` reads the tag back from source
and re-derives the classification, so results arriving from the daemon or a
cache replay — paths that never went through `in_development_adjust` in this
process — are still counted correctly.

The neutralised `skipped` is floored at 1 even when the failure arrived as a
timeout (where `failed == 0`), because a neutralised file reporting
`skipped=0` would be indistinguishable from a file that was never in
development, and would vanish from the totals.

## API exposed for the sibling lanes

`src/lib/nogc_sync_mut/spec/in_development.spl` is **pure** — text in,
verdict out, no externs, so it adds no direct `rt_*` call site to the
ratchet. Callers holding a path do their own read.

Re-exported from `std.spec`.

| symbol | for |
|---|---|
| `IN_DEVELOPMENT_TAG` | the tag name, spelled once |
| `spec_tags(source) -> [text]` | **canonical** `@tag:` extractor — de-duplicated, in order. Statistics and tag-listing tools call this instead of re-grepping |
| `source_has_tag(source, tag) -> bool` | exact-name membership (never substring) |
| `source_is_in_development(source) -> bool` | the predicate |
| `in_development_explicitly_targeted(path, path_explicit, requested) -> bool` | explicit-target rule |
| `InDevelopmentOutcome`, `classify_in_development(...)` | the single classifier — the rule lives here and is not re-derived by any surface |
| `IN_DEVELOPMENT_SKIP_MARKER`, `IN_DEVELOPMENT_UNEXPECTED_PASS_MARKER`, `IN_DEVELOPMENT_EXPLICIT_MARKER`, `IN_DEVELOPMENT_SUMMARY_MARKER` | stable line anchors — key off these, never off the surrounding prose |
| `in_development_skip_line`, `in_development_unexpected_pass_line`, `in_development_explicit_line`, `in_development_summary_line` | the emitted lines |

The runner additionally exposes, in `test_runner_main.spl`:
`file_is_in_development(path)`, `in_development_totals(results) -> (skipped,
unexpected)` and `print_in_development_summary(results)`.

## Where the rule is enforced

- `test_runner_main.run_single_test` → `in_development_adjust` — the single
  point **every** execution mode (interpreter / smf / native / compile /
  composite / safe) funnels through, so no mode can bypass neutralisation.
- `test_runner_main.run_test_cli` → `print_in_development_summary`, printed
  immediately after `print_summary`, on the ordinary summary surface and
  **not** behind `--verbose`.
- `test_runner_single.spl` — the explicit-path child. Prints the advisory
  only; it deliberately does **not** neutralise, because an explicit run
  must be able to show its own failure.

## Not done here (other lanes)

Applying the tag to existing tests, the statistics/reporting surface, and the
tag-listing CLI are separate lanes. They consume the API above.

## Known limits, stated rather than papered over

1. **The aggregate `SPEC FILE VERDICT:` line for a neutralised file reads
   `outcome=NOT_RUN`.** `emit_spec_file_verdicts` calls
   `light_protocol.ran_verdict_line(path, r.passed, r.failed)`, which sees
   `0, 0` for a neutralised file and classifies it NOT_RUN. This is
   cosmetic — it does **not** affect the exit code, because
   `test_file_result_outcome_class` counts `skipped` toward `examples` and
   returns `OK` (measured: a sweep over one failing tagged spec printed
   `All tests passed!`). It was deliberately not "fixed" here:
   `light_protocol` and `test_runner_types` belong to other lanes, and
   claiming `OK` on a file that produced no passing example would be a lie
   to the greenwash machinery those lanes exist to protect. A follow-up
   that gives the verdict line a first-class in-development outcome is the
   right shape, and needs those lanes' agreement.

2. **Pre-existing, unrelated: a directory sweep exits 1 after printing
   `All tests passed!`.** Measured 2026-08-23 on the deployed seed with a
   CONTROL directory containing two ordinary, untagged, trivially passing
   specs:

   ```
   Results: 2 total, 2 passed, 0 failed
   All tests passed!
   error[E1002]: function `runtime_file_rename` not found
   CONTROL_DIR rc=1
   ```

   The failure is in the post-run test-DB write, after the verdict, and
   reproduces with this change reverted. It is recorded here only so the
   in-development measurements below cannot be misread as caused by it.

## Measured results (2026-08-23, deployed seed)

| run | result |
|---|---|
| unit spec pre-fix (module removed) | `outcome=ERROR executed=0`, rc=1 |
| unit spec post-fix | `21 total, 21 passed, 0 failed`, rc=0 |
| sweep, 1 failing + 1 passing tagged fixture | `Results: 1 total, 1 passed, 0 failed, 1 skipped` / `All tests passed!` / `In-development: 1 skipped (expected to fail), 1 UNEXPECTED PASS (ready to promote)` |
| explicit path, failing tagged fixture | `IN-DEVELOPMENT EXPLICIT ...` / `Results: 1 total, 0 passed, 1 failed` / `FAIL`, rc=1 |
| control dir sweep, untagged specs | rc=1 from the pre-existing `runtime_file_rename` defect above, not from this change |
