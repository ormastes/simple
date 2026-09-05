# Cooperative Green Specification

> Tests covering Cooperative green facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Specification

## Scenarios

### Cooperative green facade

#### keeps queued work on the cooperative scheduler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps queued work on the cooperative scheduler
   - Expected: handle.is_done() is false
   - Expected: cooperative_green_ready_count() equals `before + 1`
   - Expected: cooperative_green_run_one() is true
   - Expected: handle.is_done() is true
   - Expected: handle.join() equals `5`
   - Expected: handle.join() equals `5`
   - Expected: cooperative_green_run_one() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps queued work on the cooperative scheduler")
val before = cooperative_green_ready_count()
val handle = cooperative_green_spawn(cooperative_green_value_5)
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(5)
expect(handle.join()).to_equal(5)
expect(cooperative_green_run_one()).to_equal(false)
```

</details>

#### runs multiple cooperative values

- runs multiple cooperative values
   - Expected: ran >= 2 is true
   - Expected: h1.join() equals `5`
   - Expected: h2.join() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs multiple cooperative values")
val h1 = cooperative_green_spawn(cooperative_green_value_5)
val h2 = cooperative_green_spawn(cooperative_green_value_13)
val ran = cooperative_green_run_all()
expect(ran >= 2).to_equal(true)
expect(h1.join()).to_equal(5)
expect(h2.join()).to_equal(13)
```

</details>

#### supports direct value scheduling for profile smoke workloads

- supports direct value scheduling for profile smoke workloads
   - Expected: handle.is_done() is false
   - Expected: cooperative_green_run_one() is true
   - Expected: handle.join() equals `21`
   - Expected: handle.join() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("supports direct value scheduling for profile smoke workloads")
val handle = cooperative_green_spawn_value(21)
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.join()).to_equal(21)
expect(handle.join()).to_equal(21)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Cooperative green facade.
- Cooperative green facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe7a61dbca34528779abbb655ad83b2ba5a3cbe38bd400ac803730a603bdec65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe7a61dbca34528779abbb655ad83b2ba5a3cbe38bd400ac803730a603bdec65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe7a61dbca34528779abbb655ad83b2ba5a3cbe38bd400ac803730a603bdec65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/cooperative_green_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/cooperative_green_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/cooperative_green_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps queued work on the cooperative scheduler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs multiple cooperative values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports direct value scheduling for profile smoke workloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
