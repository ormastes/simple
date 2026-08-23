# `@tag:in-development` — work-in-progress tests that are expected to fail

**Date:** 2026-08-23
**Status:** Implemented
**Owner files:** `src/lib/nogc_sync_mut/spec/in_development.spl`,
`src/app/test_runner_new/test_runner_main.spl`,
`src/app/test_runner_new/test_runner_single.spl`
**Specs:** `test/01_unit/lib/spec/in_development_tag_spec.spl` (landed,
21/21). An end-to-end runner spec is **not** landed — see "Known limits"
below.

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

### Decision 7: a tagged spec that cannot LOAD is BROKEN, and still fails the run

Added after the tree-wide tagging sweep made it urgent. Three lanes are
tagging every genuinely-unfinished failure across ~21,000 specs; without
this, every tagged spec with a syntax error, a broken import or an
unresolvable module would have become `executed=0` → `ExpectedFailure` →
a silent counted skip, **indistinguishable from a spec that merely does
not pass yet**. At a few dozen tags that is a nuisance; at that scale it
is precisely the "protection that hides debt" failure mode.

`InDevelopmentOutcome.LoadFailure` is a third class, checked **before**
the failure branch:

```
IN-DEVELOPMENT BROKEN <path> (unresolved-module) — a spec that cannot load is a DEFECT, not unfinished work; `@tag:in-development` does not excuse it
In-development: 1 skipped (expected to fail), 3 BROKEN (failed to load — FAILS the run)
```

**It still FAILS the run.** That call is deliberate. `@tag:in-development`
is a claim about the **code under test** — "this feature is not finished
yet". It is not a claim about the spec file. A spec that cannot be loaded
at all is not unfinished work, it is a **defect in the spec**, and a
defect that no assertion inside the file can ever be reached to
demonstrate. The tag buys amnesty for failing **assertions**; it must
never become a place broken files go to stop being counted.

The obvious counter-argument — a WIP spec may legitimately fail to load
because the module it imports *does not exist yet* — was considered and
rejected. That case is textually identical to a typo, so honouring it
would re-open the exact hole. The author's remedy is cheap and explicit:
stub the import, or leave the spec untagged until it loads.

Mechanically the result is returned **essentially unchanged** — the
`error` is preserved so `emit_spec_file_verdicts` still routes it through
`unrun_verdict_line` and the existing greenwash gates still see it — and
forced to at least one failure so the sweep goes red.

**Decision 5 is intact.** The discriminator is the runner's existing
`is_load_failure(error)`, which is exactly
`unrun_reason(error) != "zero-examples"`. A file that loads cleanly and
simply declares no examples is *not* broken, still classifies as
`ExpectedFailure`, and still never announces itself as ready to promote.

Ordering note, learned the hard way: `load_failed` must be read from the
RAW error **before** the `ExpectedFailure` branch clears it. The first cut
cleared `error` first, so by the time `emit_spec_file_verdicts` ran its
own `is_load_failure(r.error)` test the evidence was already gone and
every broken tagged spec printed a bare `outcome=NOT_RUN`.

## Tagging is only safe for load-clean specs

**Read this before acting on a tagging sweep report.** `@tag:in-development`
is only meaningful on a spec that **loads**. Tagging a spec that fails to
load does not neutralise it and never will — it will be reported as
`IN-DEVELOPMENT BROKEN` and will fail the run, by design (Decision 7).

So a sweep report's "tagged" count is not a count of neutralised specs.
Any tagged file that turns up in the BROKEN bucket is a spec defect that
still needs fixing, not unfinished feature work that has been parked.

### Decision 8: always print all three states, and never call it "skipped"

User directive, 2026-08-23: *"Always show all 3 states: pass, fail,
in-development — do not skip."* Two separate corrections.

**(a) The row is now unconditional.** It previously appeared only when
there was something to report, so a reader could not distinguish "no
in-development work" from "this runner does not track it" — and the
second reading is how a whole category quietly stops being looked at. The
row now always carries all three counts, even at zero, the same contract
the runner's `Results:` line already honours:

```
States: 412 passed, 0 failed, 0 in development (expected to fail)
```

The two exceptional classes are still appended only when non-zero,
because they are **events**, not resting states: an unexpected pass is an
action item (promote it) and BROKEN is a defect that fails the run.

**(b) It is no longer called a skip, in the wording OR in the bucket.**
This is a real mechanism correction, not a relabel. Decision 1 says a
tagged spec *executes* and only its verdict is neutralised, so "skipped"
misdescribed what happens and read as if the work were being hidden.

The carrier changed with the wording. Previously the neutralised count
was stored in `TestFileResult.skipped`, which put in-development into the
runner's genuine skip bucket and made it show up in `Results: … N
skipped`. A **new field `TestFileResult.in_development: i64 = 0`** now
carries it. `skipped` remains its own distinct state for work the
environment could not run (no GPU, wrong OS, `@tag:qemu`), the two are
never merged, and any genuine skips a tagged file itself reported are
preserved untouched.

That field is the one edit outside this lane's files. It is additive and
**defaulted**, so none of the ~85 existing `TestFileResult(...)`
constructor sites change; the only other edit there is adding it to the
`examples` sum in `test_file_result_outcome_class`, which is required —
without it a neutralised file has zero examples and classifies `NOT_RUN`,
which the exit-code path reads as `Unverified` (exit 5). Storing the
count in `skipped` was what had been satisfying that check before.

**Marker naming.** `IN_DEVELOPMENT_SKIP_MARKER` → `IN_DEVELOPMENT_MARKER`
and `in_development_skip_line` → `in_development_line`, so the word does
not survive in the API the stats lane consumes. The markers are also
**prefix-disjoint**: a short `"IN-DEVELOPMENT"` was tried and rejected
because it is a prefix of `"IN-DEVELOPMENT BROKEN"`, so a tool grepping
for one matched the other. The spec caught that, and now pins it.

**BROKEN is unchanged** — still red, still its own fourth class, still
printed whenever non-zero. It is not a variant of in-development.

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
| `InDevelopmentOutcome`, `classify_in_development(is_tagged, explicit, failed, passed, errored, load_failed)` | the single classifier — the rule lives here and is not re-derived by any surface. Four outcome classes plus `NotInDevelopment`; `LoadFailure` is checked before the failure branch |
| `IN_DEVELOPMENT_MARKER`, `IN_DEVELOPMENT_UNEXPECTED_PASS_MARKER`, `IN_DEVELOPMENT_EXPLICIT_MARKER`, `IN_DEVELOPMENT_BROKEN_MARKER`, `IN_DEVELOPMENT_SUMMARY_MARKER` | stable line anchors — key off these, never off the surrounding prose |
| `in_development_line`, `in_development_unexpected_pass_line`, `in_development_explicit_line`, `in_development_broken_line`, `in_development_summary_line(passed, failed, in_development, unexpected, broken)` | the emitted lines; markers are prefix-disjoint |

The runner additionally exposes, in `test_runner_main.spl`:
`file_is_in_development(path)`, `in_development_totals(results) ->
(in_development, unexpected, broken)` and
`print_in_development_summary(results)`.

**Note for the statistics lane — the first bucket is NOT `skipped`.** It
was renamed from `skipped` to `in_development`, and the values behind it
now live in `TestFileResult.in_development`, a field separate from
`TestFileResult.skipped`. Do not reintroduce the word downstream: a
tagged spec runs, and only its verdict is neutralised. `in_development_totals`
returns **three** buckets, not two. `bin/simple tags` and the `test_result.md` "In
Development" row need a separate BROKEN bucket — a broken tagged spec must
not be silently absorbed into the skip count on those surfaces either,
for the same reason it is not absorbed here.

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
| unit spec after Decision 7 | `28 total, 28 passed, 0 failed`, rc=0 |
| sweep, 1 BROKEN + 1 merely-failing tagged fixture | `IN-DEVELOPMENT BROKEN .../wip_broken_spec.spl (unresolved-module)` / `IN-DEVELOPMENT SKIP .../wip_failing_spec.spl (1 expected failure(s))` / `Results: 1 total, 0 passed, 1 failed, 1 skipped` / `In-development: 1 skipped (expected to fail), 1 BROKEN (failed to load — FAILS the run)` — **no `All tests passed!`**: the run is red, and the two classes are named and counted separately |

3. **The end-to-end runner spec is written but NOT landed — and an
   earlier version of this section was WRONG.** It first claimed the spec
   "hangs": at the time of writing, the run had produced no examples for
   ~25 minutes and its log had stopped growing, and that was recorded as
   a hang. It was not one. The run completed: **7 executed, 5 passed, 2
   failed** — it is merely very slow, because each of its seven scenarios
   spawns a nested full `simple test` sweep that itself pays a ~10s
   session setup. The wrong claim is left visible here rather than
   quietly overwritten, because "I waited and nothing happened" is not
   evidence of a hang, and treating it as such is the same
   absence-of-evidence mistake the push guards in this repo exist to
   forbid.

   The 2 real failures are both in the unexpected-pass scenarios, and
   their cause is worth recording because it is NOT a flaw in the
   classification:

   ```
   IN-DEVELOPMENT SKIP build/test_fixtures/in_development_d_.../wip_passing_spec.spl (1 expected failure(s))
   SPEC FILE VERDICT: .../wip_passing_spec.spl outcome=NOT_RUN declared>=0 executed=0 passed=0 failed=0
   ```

   The fixture written under `build/` **executed zero examples** in the
   child, so it never passed, so no `IN-DEVELOPMENT UNEXPECTED PASS` was
   emitted and the assertion correctly failed. The byte-identical fixture
   placed under `test/` passes and does emit the line (measured, see the
   table above). So the spec's fixture LOCATION is wrong, not the feature.

   **The genuine limitation this exposed is now FIXED — see Decision 7.**

   The spec is not landed until its fixtures are relocated and it is
   green, because landing a red spec reddens the tree for every other
   lane. The retry should also collapse the seven nested sweeps into one
   sweep over a single fixture directory asserting all four behaviours
   from that one invocation, which removes most of the runtime.
