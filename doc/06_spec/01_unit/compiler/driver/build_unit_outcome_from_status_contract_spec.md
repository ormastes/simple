# The build-side outcome contract, pinned at `BuildUnitOutcome.from_status`

> `ParallelBuilder.build_supervised()` (`driver_build/parallel.spl:680`) is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# The build-side outcome contract, pinned at `BuildUnitOutcome.from_status`

`ParallelBuilder.build_supervised()` (`driver_build/parallel.spl:680`) is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Contract guard for an as-yet-UNWIRED classifier |
| Source | `test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`ParallelBuilder.build_supervised()` (`driver_build/parallel.spl:680`) is
complete and has **zero callers**. Every classification decision it will make
runs through `BuildUnitOutcome.from_status`, and an unexercised classifier is
exactly where silent drift lives: nothing today would notice if 139 quietly
started reporting TERMINATED, or if a SIGTERM began counting as a build failure.

This spec fences the contract now, so that when the supervisor is wired the
behaviour it inherits is already fixed. The audience is whoever wires it, and
whoever is later tempted to "simplify" the six categories into two.

## Scope and Preconditions

Pure unit coverage of the RECORD constructor `BuildUnitOutcome.from_status` and
the `BuildOutcomeSet` aggregate counters. Sibling spec
`build_outcome_classification_spec.spl` covers the free function
`build_outcome_classify_status` and the summary text; this one covers the
constructor callers actually use, the aggregate arithmetic, and the OK/artifact
join. No process spawning, no filesystem, no compiler invocation.

Every expected value below is written as an absolute literal — `139` is asserted
to yield the literal text `"CRASHED"`, never compared against another call into
the same code path that produced it.

## Expected Outcome

A child that died by signal N arrives as 128+N from the supervising shell
wrapper (`parallel_supervised_argv`, `parallel.spl:72`). SIGSEGV(139) and
SIGABRT(134) are CRASHED and count as failures — as is an unbudgeted
SIGKILL(137), since only SIGTERM(15) is treated as external. SIGTERM(143) is
TERMINATED, a 137 the supervisor budget-killed is TIMEOUT, and neither of
those two ever reaches the failure count — `earlyoom` on this zero-swap host SIGTERMs
`simple` at 10% memory, so counting a memory kill as a build failure would
manufacture REDs that no code change can clear. A unit the build never reached
is recorded NOT_RUN, never silently absent. And an OK unit requires exit 0 AND
its declared artifact on disk: a clean exit that produced nothing is an ERROR.

## Scenarios

### a dead child's 128+N status becomes exactly one build outcome class

#### reports SIGSEGV (139) as CRASHED, carrying signal 11 and the raw status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports SIGSEGV (139) as CRASHED, carrying signal 11 and the raw status
   - Expected: record.label() equals `CRASHED`
   - Expected: record.signal_num equals `11`
   - Expected: record.status equals `139`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports SIGSEGV (139) as CRASHED, carrying signal 11 and the raw status")
val record = outcome_for(139, false)
expect(record.label()).to_equal("CRASHED")
expect(record.signal_num).to_equal(11)
expect(record.status).to_equal(139)
assert_false(record.is_ok())
```

</details>

#### reports SIGABRT (134) as CRASHED, carrying signal 6

- reports SIGABRT (134) as CRASHED, carrying signal 6
   - Expected: record.label() equals `CRASHED`
   - Expected: record.signal_num equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports SIGABRT (134) as CRASHED, carrying signal 6")
val record = outcome_for(134, false)
expect(record.label()).to_equal("CRASHED")
expect(record.signal_num).to_equal(6)
```

</details>

#### reports SIGTERM (143) as TERMINATED, never CRASHED

- reports SIGTERM (143) as TERMINATED, never CRASHED
   - Expected: record.label() equals `TERMINATED`
   - Expected: record.signal_num equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports SIGTERM (143) as TERMINATED, never CRASHED")
val record = outcome_for(143, false)
expect(record.label()).to_equal("TERMINATED")
expect(record.signal_num).to_equal(15)
```

</details>

#### reports an unbudgeted SIGKILL (137) as CRASHED, not TERMINATED

- reports an unbudgeted SIGKILL (137) as CRASHED, not TERMINATED
   - Expected: record.label() equals `CRASHED`
   - Expected: record.signal_num equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an unbudgeted SIGKILL (137) as CRASHED, not TERMINATED")
# Deliberate asymmetry, and the reason TERMINATED is safe to exempt from
# the failure count: only SIGTERM (15) is treated as external. A SIGKILL
# the supervisor did not schedule is indistinguishable from the compiler
# dying, so it stays a failure. `earlyoom` here sends SIGTERM, which is
# the path that must never be a failure; a raw SIGKILL is not that path.
val record = outcome_for(137, false)
expect(record.label()).to_equal("CRASHED")
expect(record.signal_num).to_equal(9)
```

</details>

#### reports the same 137 as TIMEOUT when the supervisor killed it on its budget

- reports the same 137 as TIMEOUT when the supervisor killed it on its budget
   - Expected: record.label() equals `TIMEOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the same 137 as TIMEOUT when the supervisor killed it on its budget")
# The budget is the fact that matters, not the SIGKILL that enforced it.
val record = outcome_for(137, true)
expect(record.label()).to_equal("TIMEOUT")
```

</details>

#### reports a clean exit 0 as OK with no signal recorded

- reports a clean exit 0 as OK with no signal recorded
   - Expected: record.label() equals `OK`
   - Expected: record.signal_num equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a clean exit 0 as OK with no signal recorded")
val record = outcome_for(0, false)
expect(record.label()).to_equal("OK")
expect(record.signal_num).to_equal(0)
assert_true(record.is_ok())
```

</details>

#### reports any other clean non-zero exit as ERROR, not as a crash

- reports any other clean non-zero exit as ERROR, not as a crash
   - Expected: outcome_for(1, false).label() equals `ERROR`
   - Expected: outcome_for(2, false).label() equals `ERROR`
   - Expected: outcome_for(64, false).label() equals `ERROR`
   - Expected: outcome_for(-1, false).label() equals `ERROR`
   - Expected: outcome_for(1, false).signal_num equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports any other clean non-zero exit as ERROR, not as a crash")
expect(outcome_for(1, false).label()).to_equal("ERROR")
expect(outcome_for(2, false).label()).to_equal("ERROR")
expect(outcome_for(64, false).label()).to_equal("ERROR")
# -1 is the spawn-failure sentinel; it is not a 128+N encoding.
expect(outcome_for(-1, false).label()).to_equal("ERROR")
expect(outcome_for(1, false).signal_num).to_equal(0)
```

</details>

### TERMINATED and TIMEOUT never reach the failure count

#### counts a SIGSEGV and a SIGABRT as two failures and nothing else

- counts a SIGSEGV and a SIGABRT as two failures and nothing else
   - Expected: set.failure_count() equals `2`
   - Expected: set.unverified_count() equals `0`
   - Expected: set.ok_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts a SIGSEGV and a SIGABRT as two failures and nothing else")
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.from_status(1, "seg.spl", 139, false, 5, 0, ""))
set.record(BuildUnitOutcome.from_status(2, "abort.spl", 134, false, 5, 0, ""))
expect(set.failure_count()).to_equal(2)
expect(set.unverified_count()).to_equal(0)
expect(set.ok_count()).to_equal(0)
```

</details>

<details>
<summary>Advanced: counts an earlyoom SIGTERM as unverified and as ZERO failures</summary>

#### counts an earlyoom SIGTERM as unverified and as ZERO failures

- counts an earlyoom SIGTERM as unverified and as ZERO failures
   - Expected: set.failure_count() equals `0`
   - Expected: set.unverified_count() equals `1`
   - Expected: set.ok_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts an earlyoom SIGTERM as unverified and as ZERO failures")
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.ok(1, "good.spl", 5, 0))
set.record(BuildUnitOutcome.from_status(2, "oomed.spl", 143, false, 5, 0, ""))
expect(set.failure_count()).to_equal(0)
expect(set.unverified_count()).to_equal(1)
expect(set.ok_count()).to_equal(1)
expect(set.paths_in(BuildOutcomeKind.TERMINATED)).to_contain("oomed.spl")
```

</details>


</details>

#### counts a budget timeout as unverified and as ZERO failures

- counts a budget timeout as unverified and as ZERO failures
   - Expected: set.failure_count() equals `0`
   - Expected: set.unverified_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts a budget timeout as unverified and as ZERO failures")
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.from_status(1, "slow.spl", 137, true, 900, 0, ""))
expect(set.failure_count()).to_equal(0)
expect(set.unverified_count()).to_equal(1)
```

</details>

#### keeps the two unverified classes out of the failure count even in a mixed build

- keeps the two unverified classes out of the failure count even in a mixed build
   - Expected: set.len() equals `6`
   - Expected: set.ok_count() equals `1`
   - Expected: set.failure_count() equals `2`
   - Expected: set.unverified_count() equals `2`
   - Expected: set.not_run_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the two unverified classes out of the failure count even in a mixed build")
# 6 units: 1 OK, 1 ERROR, 1 CRASHED, 1 TERMINATED, 1 TIMEOUT, 1 NOT_RUN.
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.ok(1, "a.spl", 5, 0))
set.record(BuildUnitOutcome.from_status(2, "b.spl", 1, false, 5, 0, "type error"))
set.record(BuildUnitOutcome.from_status(3, "c.spl", 139, false, 5, 0, ""))
set.record(BuildUnitOutcome.from_status(4, "d.spl", 143, false, 5, 0, ""))
set.record(BuildUnitOutcome.from_status(5, "e.spl", 137, true, 5, 0, ""))
set.record(BuildUnitOutcome.not_run(6, "f.spl"))
expect(set.len()).to_equal(6)
expect(set.ok_count()).to_equal(1)
expect(set.failure_count()).to_equal(2)
expect(set.unverified_count()).to_equal(2)
expect(set.not_run_count()).to_equal(1)
assert_false(set.all_ok())
```

</details>

#### classifies each kind as failure or unverified but never as both

- classifies each kind as failure or unverified but never as both


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies each kind as failure or unverified but never as both")
assert_true(build_outcome_is_failure(BuildOutcomeKind.ERROR))
assert_true(build_outcome_is_failure(BuildOutcomeKind.CRASHED))
assert_false(build_outcome_is_failure(BuildOutcomeKind.TERMINATED))
assert_false(build_outcome_is_failure(BuildOutcomeKind.TIMEOUT))
assert_true(build_outcome_is_unverified(BuildOutcomeKind.TERMINATED))
assert_true(build_outcome_is_unverified(BuildOutcomeKind.TIMEOUT))
assert_false(build_outcome_is_unverified(BuildOutcomeKind.CRASHED))
assert_false(build_outcome_is_unverified(BuildOutcomeKind.NOT_RUN))
```

</details>

### a unit the build never reached is stated, never silently missing

#### records NOT_RUN with the reason instead of omitting the unit

- records NOT_RUN with the reason instead of omitting the unit
   - Expected: record.label() equals `NOT_RUN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records NOT_RUN with the reason instead of omitting the unit")
val record = BuildUnitOutcome.not_run(9, "never.spl")
expect(record.label()).to_equal("NOT_RUN")
expect(record.diagnostics).to_contain("never started")
assert_false(record.is_ok())
```

</details>

#### keeps an unreached unit present in the set, so the total still covers it

- keeps an unreached unit present in the set, so the total still covers it
   - Expected: set.len() equals `2`
   - Expected: set.not_run_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps an unreached unit present in the set, so the total still covers it")
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.ok(1, "ran.spl", 5, 0))
set.record(BuildUnitOutcome.not_run(2, "never.spl"))
expect(set.len()).to_equal(2)
assert_true(set.has_path("never.spl"))
expect(set.not_run_count()).to_equal(1)
```

</details>

#### counts NOT_RUN as neither a failure nor an unverified kill

- counts NOT_RUN as neither a failure nor an unverified kill
   - Expected: set.failure_count() equals `0`
   - Expected: set.unverified_count() equals `0`
   - Expected: set.not_run_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts NOT_RUN as neither a failure nor an unverified kill")
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.not_run(1, "never.spl"))
expect(set.failure_count()).to_equal(0)
expect(set.unverified_count()).to_equal(0)
expect(set.not_run_count()).to_equal(1)
```

</details>

### OK requires exit 0 AND the declared artifact on disk

#### records a clean exit with a missing artifact as ERROR, never OK

- records a clean exit with a missing artifact as ERROR, never OK
   - Expected: set.ok_count() equals `0`
   - Expected: set.failure_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records a clean exit with a missing artifact as ERROR, never OK")
# This is the join the supervisor performs before it may call
# `BuildUnitOutcome.ok`. Modelled here with the same status the
# supervisor substitutes (1) so the fabricated-success path is fenced.
val set = BuildOutcomeSet.empty()
set.record(BuildUnitOutcome.from_status(
    1, "ghost.spl", 1, false, 5, 0,
    "exit 0 but declared artifact is missing: build/ghost.o"))
expect(set.ok_count()).to_equal(0)
expect(set.failure_count()).to_equal(1)
expect(set.paths_in(BuildOutcomeKind.ERROR)).to_contain("ghost.spl")
```

</details>

#### carries the missing-artifact reason so the unit is attributable

- carries the missing-artifact reason so the unit is attributable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries the missing-artifact reason so the unit is attributable")
val record = BuildUnitOutcome.from_status(
    1, "ghost.spl", 1, false, 5, 0,
    "exit 0 but declared artifact is missing: build/ghost.o")
expect(record.diagnostics).to_contain("declared artifact is missing")
expect(record.attribution_line()).to_contain("ERROR")
expect(record.attribution_line()).to_contain("ghost.spl")
```

</details>

#### keeps the artifact check OUT of from_status, where the supervisor owns it

- keeps the artifact check OUT of from_status, where the supervisor owns it
   - Expected: outcome_for(0, false).label() equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the artifact check OUT of from_status, where the supervisor owns it")
# from_status sees only a wait status; it cannot know about a file. This
# pins WHERE the responsibility lives, so a future refactor cannot drop
# the check by assuming the classifier already made it.
expect(outcome_for(0, false).label()).to_equal("OK")
```

</details>

#### makes the supervisor consult the declared artifact before recording OK

- makes the supervisor consult the declared artifact before recording OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("makes the supervisor consult the declared artifact before recording OK")
val src = file_read("src/compiler/80.driver/driver_build/parallel.spl")
expect(src).to_contain("val declared = artifact_fn(unit_path)")
expect(src).to_contain("if declared != \"\" and not rt_file_exists(declared):")
expect(src).to_contain("exit 0 but declared artifact is missing")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `48ebf0cae33075ccc2f6b46d39f8a009d176deb40d7c1104dcebb0e20ee0ae88`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48ebf0cae33075ccc2f6b46d39f8a009d176deb40d7c1104dcebb0e20ee0ae88`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48ebf0cae33075ccc2f6b46d39f8a009d176deb40d7c1104dcebb0e20ee0ae88`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports SIGSEGV (139) as CRASHED, carrying signal 11 and the raw status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports SIGABRT (134) as CRASHED, carrying signal 6' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports SIGTERM (143) as TERMINATED, never CRASHED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
