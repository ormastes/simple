# Collect-all must not OOM the run it is reporting on

> R3 says a build must reach the END of the source list and report every failure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collect-all must not OOM the run it is reporting on

R3 says a build must reach the END of the source list and report every failure.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Instance spec — R9 of `doc/02_requirements/compiler/supervised_builder.md` |
| Source | `test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

R3 says a build must reach the END of the source list and report every failure.
On a codebase with a *systemic* defect — exactly the case where running to the
end matters most — that requirement has a failure mode of its own.

Measured 2026-08-17 on a real stage-3 run: at **124 of 619 files** the build had
accumulated **2,926 errors** with RSS climbing **~1 GB per 30 seconds** (8.0 →
15.1 GB across six samples). Extrapolated to the full set: ~14,500 errors and
+25-30 GB. `earlyoom` fires at 10% free on this host and had already killed a
bootstrap that day. Unbounded retention of diagnostic TEXT converts a complete
error census into **no census at all**.

The audience is anyone tempted to "simplify" the retention split — in particular
anyone tempted to derive the count from the retained text.

## Scope and Preconditions

Four properties, each pinned separately because they fail independently:

1. Retained TEXT is bounded (this is what bounds memory).
2. The COUNT is **exact and uncapped** — a truncated count lies about the SIZE of
   the problem, which is strictly worse than truncated text.
3. Discarded text is **spilled to a log**, not dropped and not held on the heap.
4. The summary **states the policy**, so a reader can tell "10 problems" from
   "10 of 1948 problems".

The pre-existing `[hir-fatal-count] ... shown=10` cap bounded DISPLAY only; the
count kept rising while memory kept growing. That is the bug this spec fences.

## Expected Outcome

A unit carrying 1,948 diagnostic lines retains 10 of them, reports
`total=1948` exactly, spills the remainder to the log, and says
`shown=10 retained=10 total=1948` in the summary.

## Scenarios

### the diagnostic COUNT is exact and never capped

#### reports the true total for a unit far past the retention cap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the true total for a unit far past the retention cap
   - Expected: outcome_with(1948).diagnostic_total equals `1948`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the true total for a unit far past the retention cap")
# 1948 is the shape of the real measurement: a count that must survive
# verbatim even though almost none of its text does.
expect(outcome_with(1948).diagnostic_total).to_equal(1948)
```

</details>

#### does not derive the total from the retained text

- does not derive the total from the retained text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not derive the total from the retained text")
# The defining mistake: counting after capping. If these two were the
# same number the census would silently under-report by 99%.
val outcome = outcome_with(1948)
assert_true(outcome.diagnostic_total > outcome.diagnostic_retained)
```

</details>

#### leaves a small unit completely untruncated

- leaves a small unit completely untruncated
   - Expected: outcome.diagnostic_total equals `3`
   - Expected: outcome.diagnostic_retained equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves a small unit completely untruncated")
val outcome = outcome_with(3)
expect(outcome.diagnostic_total).to_equal(3)
expect(outcome.diagnostic_retained).to_equal(3)
```

</details>

### the retained TEXT is bounded, which is what bounds memory

#### keeps at most the cap even when a thousand times more arrived

- keeps at most the cap even when a thousand times more arrived
   - Expected: outcome_with(1948).diagnostic_retained equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps at most the cap even when a thousand times more arrived")
expect(outcome_with(1948).diagnostic_retained).to_equal(10)
```

</details>

#### keeps the FIRST diagnostics, not the last

- keeps the FIRST diagnostics, not the last


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the FIRST diagnostics, not the last")
# The first error of a systemic failure is the one that explains the
# other 1,947; keeping the tail would keep the least useful end.
assert_true(outcome_with(1948).diagnostics.contains("error[E1]:"))
```

</details>

#### grows the retained text sublinearly in the number of diagnostics

- grows the retained text sublinearly in the number of diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("grows the retained text sublinearly in the number of diagnostics")
# The property under test stated as a measurement rather than an
# assertion about internals: 100x the diagnostics must NOT be 100x the
# retained bytes. Without a retention cap this is what climbed 1 GB/30s.
val small = outcome_with(20).diagnostics.len()
val huge = outcome_with(2000).diagnostics.len()
assert_true(huge < small * 3)
```

</details>

### discarded text is spilled to the log, not lost and not held

#### writes the full diagnostic text to the spill log

- writes the full diagnostic text to the spill log


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes the full diagnostic text to the spill log")
val log_path = build_outcome_spill_log_path()
if rt_file_exists(log_path):
    rt_file_delete(log_path)
build_outcome_retain_diagnostics("src/spilled.spl", many_diagnostics(50))
assert_true(rt_file_exists(log_path))
val spilled = rt_file_read_text(log_path) ?? ""
# A line well past the retention cap must be recoverable from the log.
assert_true(spilled.contains("systemic defect number 47"))
assert_true(spilled.contains("src/spilled.spl"))
```

</details>

#### says in the retained text where the rest went

- says in the retained text where the rest went


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("says in the retained text where the rest went")
val kept = build_outcome_retain_diagnostics("src/x.spl", many_diagnostics(50))
assert_true(kept.contains("spilled to"))
```

</details>

### the summary states the retention policy

#### reports shown, retained and the exact total together

- reports shown, retained and the exact total together


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports shown, retained and the exact total together")
val outcomes = BuildOutcomeSet.empty()
outcomes.record(outcome_with(1948))
val summary = outcomes.summary()
assert_true(summary.contains("total=1948"))
assert_true(summary.contains("retained=10"))
assert_true(summary.contains("shown=10"))
```

</details>

#### stays silent about retention when nothing was truncated

- stays silent about retention when nothing was truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays silent about retention when nothing was truncated")
# Noise on the common path trains readers to ignore the line that
# matters, so the policy note appears only when it is TRUE.
val outcomes = BuildOutcomeSet.empty()
outcomes.record(outcome_with(2))
assert_false(outcomes.summary().contains("reason-retention"))
```

</details>

### the free helpers agree with the record

#### counts and caps identically to from_status

- counts and caps identically to from_status
   - Expected: build_outcome_count_diagnostic_lines(blob) equals `77`
   - Expected: build_outcome_retained_diagnostic_count(blob) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts and caps identically to from_status")
val blob = many_diagnostics(77)
expect(build_outcome_count_diagnostic_lines(blob)).to_equal(77)
expect(build_outcome_retained_diagnostic_count(blob)).to_equal(10)
```

</details>

#### counts an empty diagnostic as zero, not one

- counts an empty diagnostic as zero, not one
   - Expected: build_outcome_count_diagnostic_lines("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts an empty diagnostic as zero, not one")
expect(build_outcome_count_diagnostic_lines("")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DRIVER-BUILD-OUTCOME-009`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7d51b080eca843f75369e8d744641b02388d49eb28ce823988afa386668b0f5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d51b080eca843f75369e8d744641b02388d49eb28ce823988afa386668b0f5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d51b080eca843f75369e8d744641b02388d49eb28ce823988afa386668b0f5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the true total for a unit far past the retention cap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not derive the total from the retained text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_outcome_bounded_accumulation_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves a small unit completely untruncated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
