# Six poisoned modules, reported correctly in ONE run

> The acceptance criterion for a crash-safe build is not "the build survives a bad

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Six poisoned modules, reported correctly in ONE run

The acceptance criterion for a crash-safe build is not "the build survives a bad

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Instance spec — the acceptance criterion for the crash-safe build slice |
| Source | `test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The acceptance criterion for a crash-safe build is not "the build survives a bad
module". It is: **one run reaches the END of a poisoned work list and reports
every unit in it, with the categories disjoint.** A build that dies on the first
bad unit makes every subsequent defect cost another full build to discover — the
recurring defect recorded in
`test/01_unit/compiler/driver/build_phase_collect_all_contract_spec.spl`.

This spec drives the six-module fixture in
`test/fixtures/build_supervisor_poisoned/` through the shared outcome vocabulary
in `compiler.driver.driver_build.build_outcome`, using REAL subprocesses with
REAL wait statuses.

The audience is anyone changing the supervisor's unit loop or its
classification.

## Scope and Preconditions

Six units, one build unit each, four disjoint expected categories:

| unit | fixture                | expected | how it is induced |
|------|------------------------|----------|-------------------|
| 1 | `unit1_parse_error.spl` | ERROR    | REAL — `bin/simple run` on genuinely unparseable source, measured exit 1 |
| 2 | `unit2_segfault.spl`    | CRASHED  | real SIGSEGV of a real child (status 139) — **not** a compiler segfault |
| 3 | `unit3_oom.spl`         | CRASHED  | real SIGKILL of a real child (status 137) — **not** a real OOM |
| 4 | `unit4_timeout.spl`     | TIMEOUT  | REAL — a child that genuinely outruns a 1s per-unit budget |
| 5 | `unit5_clean.spl`       | OK       | REAL — `bin/simple run`, measured exit 0 |
| 6 | `unit6_clean.spl`       | OK       | REAL — `bin/simple run`, measured exit 0 |

**Stated plainly, because a fixture that overclaims is worse than none:** units 2
and 3 do not make the *compiler* crash. No .spl source is known to segfault it on
demand, and a genuine compile-time OOM on this host would be reaped by
`earlyoom` as SIGTERM (143 = TERMINATED = UNVERIFIED), which is a different
category from the one under test. What is real in units 2 and 3 is the part that
matters here: the supervisor observes an actual signal death of an actual child
and must classify and survive it. Each fixture file repeats this caveat in its
own header.

### Why the build command is wrapped

`shell()` (`std.nogc_sync_mut.io.process_ops`) reports **-1** for *every* signal
death — SIGSEGV, SIGKILL and SIGTERM are indistinguishable through it (measured).
A supervisor reading that channel could not tell CRASHED from TERMINATED, i.e.
could not tell a compiler bug from earlyoom. So every unit's command is wrapped
so the outer shell reports the POSIX `128+N` status as its own ordinary exit
code, which the runtime does preserve. That channel contract is itself pinned as
a defect class in
`build_supervisor_status_channel_fidelity_spec.spl`.

## Expected Outcome

ONE pass over the list produces six records: OK=2, ERROR=1, CRASHED=2,
TIMEOUT=1, TERMINATED=0, NOT_RUN=0. The last unit is reached. TIMEOUT is
excluded from `failure_count()`. The summary is byte-identical across two
independent passes.

The negative control at the bottom runs the SAME six units through a supervisor
that returns on the first non-OK unit — the unfixed behaviour — and asserts it is
measurably worse: it reports fewer units, never reaches the clean tail, and
leaves units NOT_RUN.

## Scenarios

### one run reports all six poisoned units

#### records exactly one outcome per unit and reaches the last one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records exactly one outcome per unit and reaches the last one
   - Expected: outcomes.len() equals `6`
   - Expected: outcomes.count_of(BuildOutcomeKind.NOT_RUN) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records exactly one outcome per unit and reaches the last one")
val paths = poisoned_unit_paths()
val outcomes = supervise_collect_all(paths)
expect(outcomes.len()).to_equal(6)
# Reaching the LAST unit is the acceptance criterion in one assertion.
assert_true(outcomes.has_path("{FIXTURE_DIR}/unit6_clean.spl"))
expect(outcomes.count_of(BuildOutcomeKind.NOT_RUN)).to_equal(0)
```

</details>

#### assigns the four expected categories, disjointly

- assigns the four expected categories, disjointly
   - Expected: outcomes.count_of(BuildOutcomeKind.OK) equals `2`
   - Expected: outcomes.count_of(BuildOutcomeKind.ERROR) equals `1`
   - Expected: outcomes.count_of(BuildOutcomeKind.CRASHED) equals `2`
   - Expected: outcomes.count_of(BuildOutcomeKind.TIMEOUT) equals `1`
   - Expected: outcomes.count_of(BuildOutcomeKind.TERMINATED) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("assigns the four expected categories, disjointly")
val outcomes = supervise_collect_all(poisoned_unit_paths())
expect(outcomes.count_of(BuildOutcomeKind.OK)).to_equal(2)
expect(outcomes.count_of(BuildOutcomeKind.ERROR)).to_equal(1)
expect(outcomes.count_of(BuildOutcomeKind.CRASHED)).to_equal(2)
expect(outcomes.count_of(BuildOutcomeKind.TIMEOUT)).to_equal(1)
# 143/SIGTERM is a DIFFERENT category and nothing here produces it.
expect(outcomes.count_of(BuildOutcomeKind.TERMINATED)).to_equal(0)
```

</details>

#### puts each named fixture in the category it was built to produce

- puts each named fixture in the category it was built to produce
   - Expected: crashed[0] equals `{FIXTURE_DIR}/unit2_segfault.spl`
   - Expected: crashed[1] equals `{FIXTURE_DIR}/unit3_oom.spl`
   - Expected: ok[0] equals `{FIXTURE_DIR}/unit5_clean.spl`
   - Expected: ok[1] equals `{FIXTURE_DIR}/unit6_clean.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("puts each named fixture in the category it was built to produce")
val outcomes = supervise_collect_all(poisoned_unit_paths())
expect(outcomes.paths_in(BuildOutcomeKind.ERROR)[0])
    .to_equal("{FIXTURE_DIR}/unit1_parse_error.spl")
val crashed = outcomes.paths_in(BuildOutcomeKind.CRASHED)
expect(crashed[0]).to_equal("{FIXTURE_DIR}/unit2_segfault.spl")
expect(crashed[1]).to_equal("{FIXTURE_DIR}/unit3_oom.spl")
expect(outcomes.paths_in(BuildOutcomeKind.TIMEOUT)[0])
    .to_equal("{FIXTURE_DIR}/unit4_timeout.spl")
val ok = outcomes.paths_in(BuildOutcomeKind.OK)
expect(ok[0]).to_equal("{FIXTURE_DIR}/unit5_clean.spl")
expect(ok[1]).to_equal("{FIXTURE_DIR}/unit6_clean.spl")
```

</details>

#### counts the timed-out unit as UNVERIFIED, never as a failure

- counts the timed-out unit as UNVERIFIED, never as a failure
   - Expected: outcomes.failure_count() equals `3`
   - Expected: outcomes.unverified_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts the timed-out unit as UNVERIFIED, never as a failure")
val outcomes = supervise_collect_all(poisoned_unit_paths())
# 1 ERROR + 2 CRASHED. The TIMEOUT is deliberately NOT here: a unit that
# was never given time to answer has not been judged.
expect(outcomes.failure_count()).to_equal(3)
expect(outcomes.unverified_count()).to_equal(1)
```

</details>

#### names every non-OK unit in a deterministic summary

- names every non-OK unit in a deterministic summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("names every non-OK unit in a deterministic summary")
val outcomes = supervise_collect_all(poisoned_unit_paths())
val summary = outcomes.summary()
for path in poisoned_unit_paths():
    assert_true(outcomes.has_path(path))
assert_true(summary.contains("OK=2"))
assert_true(summary.contains("ERROR=1"))
assert_true(summary.contains("CRASHED=2"))
assert_true(summary.contains("TIMEOUT=1"))
assert_true(summary.contains("unit4_timeout.spl"))
# The UNVERIFIED categories must SAY they are infrastructure.
assert_true(summary.contains("UNVERIFIED"))
```

</details>

#### produces a byte-identical summary on a second independent run

- produces a byte-identical summary on a second independent run
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces a byte-identical summary on a second independent run")
# Units finish in whatever order the host schedules them; the summary
# must not. Two full passes, compared byte-for-byte.
val first = supervise_collect_all(poisoned_unit_paths()).summary()
val second = supervise_collect_all(poisoned_unit_paths()).summary()
expect(first).to_equal(second)
```

</details>

### negative control: returning on the first failure is measurably worse

#### reports strictly fewer real outcomes than the collect-all supervisor

- reports strictly fewer real outcomes than the collect-all supervisor
   - Expected: fixed.not_run_count() equals `0`
   - Expected: unfixed.not_run_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports strictly fewer real outcomes than the collect-all supervisor")
val paths = poisoned_unit_paths()
val fixed = supervise_collect_all(paths)
val unfixed = supervise_return_on_first_failure(paths)
# Both name six units — the unfixed one only because it is honest enough
# to state NOT_RUN. What it cannot do is JUDGE them.
expect(fixed.not_run_count()).to_equal(0)
assert_true(unfixed.not_run_count() > 0)
expect(unfixed.not_run_count()).to_equal(5)
```

</details>

#### never discovers the defects that sit behind the first one

- never discovers the defects that sit behind the first one
   - Expected: unfixed.count_of(BuildOutcomeKind.CRASHED) equals `0`
   - Expected: unfixed.count_of(BuildOutcomeKind.TIMEOUT) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never discovers the defects that sit behind the first one")
val unfixed = supervise_return_on_first_failure(poisoned_unit_paths())
# The two real crashers are behind the parse error and stay invisible.
expect(unfixed.count_of(BuildOutcomeKind.CRASHED)).to_equal(0)
expect(unfixed.count_of(BuildOutcomeKind.TIMEOUT)).to_equal(0)
```

</details>

#### never reaches the clean tail, so a green module reads as unbuilt

- never reaches the clean tail, so a green module reads as unbuilt
   - Expected: unfixed.count_of(BuildOutcomeKind.OK) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never reaches the clean tail, so a green module reads as unbuilt")
val unfixed = supervise_return_on_first_failure(poisoned_unit_paths())
expect(unfixed.count_of(BuildOutcomeKind.OK)).to_equal(0)
val not_run = unfixed.paths_in(BuildOutcomeKind.NOT_RUN)
assert_true(not_run.contains("{FIXTURE_DIR}/unit6_clean.spl"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DRIVER-BUILD-OUTCOME-003`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `522b4e383b424ff67a952668134d08d231e5c759222104797b367eb55323cc2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `522b4e383b424ff67a952668134d08d231e5c759222104797b367eb55323cc2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `522b4e383b424ff67a952668134d08d231e5c759222104797b367eb55323cc2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records exactly one outcome per unit and reaches the last one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns the four expected categories, disjointly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'puts each named fixture in the category it was built to produce' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
