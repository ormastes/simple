# Build outcome classification and collect-all accumulation

> A build must be able to say *what happened to every unit of work*, in categories

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Build outcome classification and collect-all accumulation

A build must be able to say *what happened to every unit of work*, in categories

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Requirement guard (R2/R3/R4 of |
| Source | `test/01_unit/compiler/driver/build_outcome_classification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A build must be able to say *what happened to every unit of work*, in categories
that never collapse into one another, and it must reach the end of the unit list
before it decides the build failed. Two distinct defects motivated this:

1. **Fail-fast across units.** `driver_aot_native_output.spl` carried 24
   immediate `return CompileResult.CodegenError(...)` sites, so the first bad
   module abandoned every remaining one and each defect cost a full ~20-minute
   bootstrap run to locate.
2. **A death was reported as a compiler verdict.** `earlyoom` on this host runs
   `--prefer ^(simple|...) --avoid ^(claude|...)` and actively SIGTERMs `simple`.
   A stage-3 run ended `exit 143` at 26 minutes and was read as a compiler
   failure. It was not: it was infrastructure, and the units in flight were
   **UNVERIFIED**, not failed. Conflating the two manufactures phantom compiler
   bugs — it happened on this repo today.

The audience is anyone extending the builder or tempted to fold `TERMINATED` /
`TIMEOUT` into a general failure count.

## Scope and Preconditions

Pure unit coverage of `compiler.driver.driver_build.build_outcome`: the
wait-status classifier, the per-unit record, the accumulator's counting and
category queries, `all_ok()`, and the determinism of the formatted summary. No
process spawning, no filesystem, no compiler invocation — this is the vocabulary,
not the supervisor that uses it.

## Expected Outcome

Each status maps to exactly one category; a `TERMINATED` unit raises the
unverified count and leaves the failure count untouched; a six-unit set with two
clean units still names all four poisoned ones; and two `summary()` calls over
the same set return byte-identical text so two runs can be diffed.

## Scenarios

### build outcome status classification

#### maps a clean exit to OK and a clean non-zero exit to ERROR

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps a clean exit to OK and a clean non-zero exit to ERROR
   - Expected: build_outcome_kind_label(build_outcome_classify_status(0, false)) equals `OK`
   - Expected: build_outcome_kind_label(build_outcome_classify_status(1, false)) equals `ERROR`
   - Expected: build_outcome_kind_label(build_outcome_classify_status(2, false)) equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps a clean exit to OK and a clean non-zero exit to ERROR")
expect(build_outcome_kind_label(build_outcome_classify_status(0, false))).to_equal("OK")
expect(build_outcome_kind_label(build_outcome_classify_status(1, false))).to_equal("ERROR")
expect(build_outcome_kind_label(build_outcome_classify_status(2, false))).to_equal("ERROR")
```

</details>

<details>
<summary>Advanced: maps 128+N signal deaths to CRASHED for SIGSEGV, SIGABRT and SIGKILL/OOM</summary>

#### maps 128+N signal deaths to CRASHED for SIGSEGV, SIGABRT and SIGKILL/OOM

- maps 128+N signal deaths to CRASHED for SIGSEGV, SIGABRT and SIGKILL/OOM
   - Expected: build_outcome_kind_label(build_outcome_classify_status(139, false)) equals `CRASHED`
   - Expected: build_outcome_kind_label(build_outcome_classify_status(134, false)) equals `CRASHED`
   - Expected: build_outcome_kind_label(build_outcome_classify_status(137, false)) equals `CRASHED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps 128+N signal deaths to CRASHED for SIGSEGV, SIGABRT and SIGKILL/OOM")
expect(build_outcome_kind_label(build_outcome_classify_status(139, false))).to_equal("CRASHED")
expect(build_outcome_kind_label(build_outcome_classify_status(134, false))).to_equal("CRASHED")
expect(build_outcome_kind_label(build_outcome_classify_status(137, false))).to_equal("CRASHED")
```

</details>


</details>

#### keeps SIGTERM (143) in its own TERMINATED category, never CRASHED

- keeps SIGTERM (143) in its own TERMINATED category, never CRASHED
   - Expected: build_outcome_kind_label(build_outcome_classify_status(143, false)) equals `TERMINATED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps SIGTERM (143) in its own TERMINATED category, never CRASHED")
# earlyoom SIGTERMs `simple` on this host. 143 is infrastructure.
expect(build_outcome_kind_label(build_outcome_classify_status(143, false))).to_equal("TERMINATED")
```

</details>

#### reports a budget overrun as TIMEOUT regardless of the enforcing signal

- reports a budget overrun as TIMEOUT regardless of the enforcing signal
   - Expected: build_outcome_kind_label(build_outcome_classify_status(137, true)) equals `TIMEOUT`
   - Expected: build_outcome_kind_label(build_outcome_classify_status(0, true)) equals `TIMEOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a budget overrun as TIMEOUT regardless of the enforcing signal")
expect(build_outcome_kind_label(build_outcome_classify_status(137, true))).to_equal("TIMEOUT")
expect(build_outcome_kind_label(build_outcome_classify_status(0, true))).to_equal("TIMEOUT")
```

</details>

#### decodes the signal number out of a 128+N status and 0 out of an exit code

- decodes the signal number out of a 128+N status and 0 out of an exit code
   - Expected: build_outcome_signal_of_status(139) equals `11`
   - Expected: build_outcome_signal_of_status(134) equals `6`
   - Expected: build_outcome_signal_of_status(137) equals `9`
   - Expected: build_outcome_signal_of_status(143) equals `15`
   - Expected: build_outcome_signal_of_status(1) equals `0`
   - Expected: build_outcome_signal_of_status(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes the signal number out of a 128+N status and 0 out of an exit code")
expect(build_outcome_signal_of_status(139)).to_equal(11)
expect(build_outcome_signal_of_status(134)).to_equal(6)
expect(build_outcome_signal_of_status(137)).to_equal(9)
expect(build_outcome_signal_of_status(143)).to_equal(15)
expect(build_outcome_signal_of_status(1)).to_equal(0)
expect(build_outcome_signal_of_status(0)).to_equal(0)
```

</details>

### TERMINATED and TIMEOUT are unverified, not failures

#### classifies TERMINATED as unverified and not a failure

- classifies TERMINATED as unverified and not a failure
   - Expected: build_outcome_is_unverified(BuildOutcomeKind.TERMINATED) is true
   - Expected: build_outcome_is_failure(BuildOutcomeKind.TERMINATED) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies TERMINATED as unverified and not a failure")
expect(build_outcome_is_unverified(BuildOutcomeKind.TERMINATED)).to_equal(true)
expect(build_outcome_is_failure(BuildOutcomeKind.TERMINATED)).to_equal(false)
```

</details>

#### classifies TIMEOUT as unverified and not a failure

- classifies TIMEOUT as unverified and not a failure
   - Expected: build_outcome_is_unverified(BuildOutcomeKind.TIMEOUT) is true
   - Expected: build_outcome_is_failure(BuildOutcomeKind.TIMEOUT) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies TIMEOUT as unverified and not a failure")
expect(build_outcome_is_unverified(BuildOutcomeKind.TIMEOUT)).to_equal(true)
expect(build_outcome_is_failure(BuildOutcomeKind.TIMEOUT)).to_equal(false)
```

</details>

#### classifies ERROR and CRASHED as failures and not unverified

- classifies ERROR and CRASHED as failures and not unverified
   - Expected: build_outcome_is_failure(BuildOutcomeKind.ERROR) is true
   - Expected: build_outcome_is_failure(BuildOutcomeKind.CRASHED) is true
   - Expected: build_outcome_is_unverified(BuildOutcomeKind.ERROR) is false
   - Expected: build_outcome_is_unverified(BuildOutcomeKind.CRASHED) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies ERROR and CRASHED as failures and not unverified")
expect(build_outcome_is_failure(BuildOutcomeKind.ERROR)).to_equal(true)
expect(build_outcome_is_failure(BuildOutcomeKind.CRASHED)).to_equal(true)
expect(build_outcome_is_unverified(BuildOutcomeKind.ERROR)).to_equal(false)
expect(build_outcome_is_unverified(BuildOutcomeKind.CRASHED)).to_equal(false)
```

</details>

#### does NOT count a SIGTERMed unit as a failure

- does NOT count a SIGTERMed unit as a failure
   - Expected: outcomes.failure_count() equals `0`
   - Expected: outcomes.unverified_count() equals `1`
   - Expected: outcomes.all_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does NOT count a SIGTERMed unit as a failure")
# The single most load-bearing assertion in this file. A set whose only
# non-OK unit was SIGTERMed has ZERO failures and ONE unverified unit.
var outcomes = BuildOutcomeSet.empty()
outcomes.record(BuildUnitOutcome.ok(1, "fixture/clean_a.spl", 12, 2048))
outcomes.record(BuildUnitOutcome.from_status(2, "fixture/killed.spl", 143,
    false, 90000, 4096, ""))
expect(outcomes.failure_count()).to_equal(0)
expect(outcomes.unverified_count()).to_equal(1)
# It is still not OK: there is no object, and fabricating one is
# forbidden, so the link must refuse.
expect(outcomes.all_ok()).to_equal(false)
```

</details>

### collect-all accumulation over the whole unit list

#### reports every poisoned unit from a six-unit fixture in one pass

- reports every poisoned unit from a six-unit fixture in one pass
   - Expected: outcomes.len() equals `6`
   - Expected: outcomes.ok_count() equals `2`
   - Expected: outcomes.count_of(BuildOutcomeKind.ERROR) equals `1`
   - Expected: outcomes.count_of(BuildOutcomeKind.CRASHED) equals `2`
   - Expected: outcomes.count_of(BuildOutcomeKind.TIMEOUT) equals `1`
   - Expected: outcomes.failure_count() + outcomes.unverified_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports every poisoned unit from a six-unit fixture in one pass")
val outcomes = fixture_six_unit_set()
expect(outcomes.len()).to_equal(6)
expect(outcomes.ok_count()).to_equal(2)
expect(outcomes.count_of(BuildOutcomeKind.ERROR)).to_equal(1)
expect(outcomes.count_of(BuildOutcomeKind.CRASHED)).to_equal(2)
expect(outcomes.count_of(BuildOutcomeKind.TIMEOUT)).to_equal(1)
# 4 poisoned units, and the count never claims six compiled.
expect(outcomes.failure_count() + outcomes.unverified_count()).to_equal(4)
```

</details>

#### names the units in a category rather than only the first

- names the units in a category rather than only the first
   - Expected: crashed.len() equals `2`
   - Expected: crashed[0] equals `fixture/bad_oom.spl`
   - Expected: crashed[1] equals `fixture/bad_segv.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names the units in a category rather than only the first")
val outcomes = fixture_six_unit_set()
val crashed = outcomes.paths_in(BuildOutcomeKind.CRASHED)
expect(crashed.len()).to_equal(2)
expect(crashed[0]).to_equal("fixture/bad_oom.spl")
expect(crashed[1]).to_equal("fixture/bad_segv.spl")
```

</details>

#### states a never-attempted unit as NOT_RUN instead of omitting it

- states a never-attempted unit as NOT_RUN instead of omitting it
   - Expected: outcomes.not_run_count() equals `1`
   - Expected: outcomes.has_path("fixture/never.spl") is true
   - Expected: outcomes.all_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("states a never-attempted unit as NOT_RUN instead of omitting it")
var outcomes = BuildOutcomeSet.empty()
outcomes.record(BuildUnitOutcome.ok(1, "fixture/clean_a.spl", 12, 2048))
outcomes.record(BuildUnitOutcome.not_run(2, "fixture/never.spl"))
expect(outcomes.not_run_count()).to_equal(1)
expect(outcomes.has_path("fixture/never.spl")).to_equal(true)
expect(outcomes.all_ok()).to_equal(false)
```

</details>

#### is all_ok only when every unit is OK

- is all_ok only when every unit is OK
   - Expected: clean.all_ok() is true
   - Expected: clean.verdict() equals ``
   - Expected: clean.all_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is all_ok only when every unit is OK")
var clean = BuildOutcomeSet.empty()
clean.record(BuildUnitOutcome.ok(1, "fixture/clean_a.spl", 12, 2048))
clean.record(BuildUnitOutcome.ok(2, "fixture/clean_b.spl", 14, 2048))
expect(clean.all_ok()).to_equal(true)
expect(clean.verdict()).to_equal("")
clean.record(BuildUnitOutcome.from_status(3, "fixture/bad_segv.spl", 139,
    false, 7, 1024, ""))
expect(clean.all_ok()).to_equal(false)
```

</details>

### the end-of-build summary is deterministic and complete

#### returns byte-identical text across two calls over the same set

- returns byte-identical text across two calls over the same set
   - Expected: outcomes.summary() equals `outcomes.summary()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns byte-identical text across two calls over the same set")
val outcomes = fixture_six_unit_set()
expect(outcomes.summary()).to_equal(outcomes.summary())
```

</details>

#### is insensitive to the order units were recorded in

- is insensitive to the order units were recorded in
   - Expected: forward.summary() equals `backward.summary()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is insensitive to the order units were recorded in")
# Units finish in whatever order the host schedules them, so insertion
# order is not reproducible; the summary must not depend on it.
var forward = BuildOutcomeSet.empty()
forward.record(BuildUnitOutcome.from_status(1, "fixture/bad_a.spl", 1, false, 1, 1, "a"))
forward.record(BuildUnitOutcome.from_status(2, "fixture/bad_b.spl", 1, false, 1, 1, "b"))
var backward = BuildOutcomeSet.empty()
backward.record(BuildUnitOutcome.from_status(2, "fixture/bad_b.spl", 1, false, 1, 1, "b"))
backward.record(BuildUnitOutcome.from_status(1, "fixture/bad_a.spl", 1, false, 1, 1, "a"))
expect(forward.summary()).to_equal(backward.summary())
```

</details>

#### names every non-OK unit and labels the unverified categories as such

- names every non-OK unit and labels the unverified categories as such
   - Expected: summary contains `fixture/bad_parse.spl`
   - Expected: summary contains `fixture/bad_segv.spl`
   - Expected: summary contains `fixture/bad_oom.spl`
   - Expected: summary contains `fixture/bad_hang.spl`
   - Expected: summary contains `UNVERIFIED`
   - Expected: summary contains `OK=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names every non-OK unit and labels the unverified categories as such")
val summary = fixture_six_unit_set().summary()
expect(summary.contains("fixture/bad_parse.spl")).to_equal(true)
expect(summary.contains("fixture/bad_segv.spl")).to_equal(true)
expect(summary.contains("fixture/bad_oom.spl")).to_equal(true)
expect(summary.contains("fixture/bad_hang.spl")).to_equal(true)
expect(summary.contains("UNVERIFIED")).to_equal(true)
# Clean units are counted, not listed: the listing is the failure report.
expect(summary.contains("OK=2")).to_equal(true)
```

</details>

#### carries counts and every failing name into the fail-closed verdict

- carries counts and every failing name into the fail-closed verdict
   - Expected: verdict contains `fixture/bad_parse.spl`
   - Expected: verdict contains `fixture/bad_segv.spl`
   - Expected: verdict contains `fixture/bad_oom.spl`
   - Expected: verdict contains `fixture/bad_hang.spl`
   - Expected: verdict contains `3 failed`
   - Expected: verdict contains `1 unverified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries counts and every failing name into the fail-closed verdict")
val verdict = fixture_six_unit_set().verdict()
expect(verdict.contains("fixture/bad_parse.spl")).to_equal(true)
expect(verdict.contains("fixture/bad_segv.spl")).to_equal(true)
expect(verdict.contains("fixture/bad_oom.spl")).to_equal(true)
expect(verdict.contains("fixture/bad_hang.spl")).to_equal(true)
# 1 ERROR + 2 CRASHED = 3 failed; the TIMEOUT is unverified, not failed.
expect(verdict.contains("3 failed")).to_equal(true)
expect(verdict.contains("1 unverified")).to_equal(true)
```

</details>

#### records per-unit attribution: id, cause, wall time and peak RSS

- records per-unit attribution: id, cause, wall time and peak RSS
   - Expected: line contains `unit=7`
   - Expected: line contains `CRASHED`
   - Expected: line contains `signal=11`
   - Expected: line contains `wall_ms=5321`
   - Expected: line contains `rss_kb=812345`
   - Expected: line contains `fixture/bad_segv.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records per-unit attribution: id, cause, wall time and peak RSS")
# This line is what was missing when stage 3 was SIGTERMed with 43 files
# left, and it answers "which file is slow" on a host where attach-based
# profiling is blocked.
val outcome = BuildUnitOutcome.from_status(7, "fixture/bad_segv.spl", 139,
    false, 5321, 812345, "")
val line = outcome.attribution_line()
expect(line.contains("unit=7")).to_equal(true)
expect(line.contains("CRASHED")).to_equal(true)
expect(line.contains("signal=11")).to_equal(true)
expect(line.contains("wall_ms=5321")).to_equal(true)
expect(line.contains("rss_kb=812345")).to_equal(true)
expect(line.contains("fixture/bad_segv.spl")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DRIVER-BUILD-OUTCOME-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94c09c19baa1cf772f57f12e4f45b3fe59d78973fdcbc21425e75b0e2428b6a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94c09c19baa1cf772f57f12e4f45b3fe59d78973fdcbc21425e75b0e2428b6a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94c09c19baa1cf772f57f12e4f45b3fe59d78973fdcbc21425e75b0e2428b6a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_outcome_classification_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_outcome_classification_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_outcome_classification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_outcome_classification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_outcome_classification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_outcome_classification_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_outcome_classification_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a clean exit to OK and a clean non-zero exit to ERROR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_outcome_classification_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps 128+N signal deaths to CRASHED for SIGSEGV, SIGABRT and SIGKILL/OOM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_outcome_classification_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps SIGTERM (143) in its own TERMINATED category, never CRASHED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
