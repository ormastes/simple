# Green Thread Value Slot Specification

> Tests covering green thread value-slot completion accounting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Thread Value Slot Specification

## Scenarios

### green thread value-slot completion accounting

#### a deferred task run does not mark an unrelated value slot done

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a deferred task run does not mark an unrelated value slot done
   - Expected: green_ready_count() equals `2`
   - Expected: v.is_done() is false
   - Expected: green_run_one() is true
   - Expected: d.is_done() is true
   - Expected: d.join() equals `42`
   - Expected: green_ready_count() equals `1`
   - Expected: v.is_done() is false
   - Expected: green_run_one() is true
   - Expected: green_ready_count() equals `0`
   - Expected: v.is_done() is true
   - Expected: v.join() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a deferred task run does not mark an unrelated value slot done")
# Drain any state left by earlier work in this process.
green_run_all()

val v = green_spawn_value(7)
val d = green_spawn(gt_answer)
expect(green_ready_count()).to_equal(2)
expect(v.is_done()).to_equal(false)

# One step: green_run_one() picks the DEFERRED task first.
expect(green_run_one()).to_equal(true)
expect(d.is_done()).to_equal(true)
expect(d.join()).to_equal(42)

# The value slot has NOT been advanced yet — one item is still
# outstanding, so is_done() must still be false.
expect(green_ready_count()).to_equal(1)
expect(v.is_done()).to_equal(false)

# Second step advances the value slot.
expect(green_run_one()).to_equal(true)
expect(green_ready_count()).to_equal(0)
expect(v.is_done()).to_equal(true)
expect(v.join()).to_equal(7)
```

</details>

#### value slots complete in spawn order

- value slots complete in spawn order
   - Expected: a.is_done() is false
   - Expected: b.is_done() is false
   - Expected: green_run_one() is true
   - Expected: a.is_done() is true
   - Expected: b.is_done() is false
   - Expected: green_run_one() is true
   - Expected: b.is_done() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("value slots complete in spawn order")
green_run_all()
val a = green_spawn_value(1)
val b = green_spawn_value(2)
expect(a.is_done()).to_equal(false)
expect(b.is_done()).to_equal(false)
expect(green_run_one()).to_equal(true)
expect(a.is_done()).to_equal(true)
expect(b.is_done()).to_equal(false)
expect(green_run_one()).to_equal(true)
expect(b.is_done()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering green thread value-slot completion accounting.
- green thread value-slot completion accounting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `af9f4cc196d6a34b6afa918e64c39debe4b023ec6ff9e456177d61033a8d6103`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af9f4cc196d6a34b6afa918e64c39debe4b023ec6ff9e456177d61033a8d6103`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af9f4cc196d6a34b6afa918e64c39debe4b023ec6ff9e456177d61033a8d6103`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a deferred task run does not mark an unrelated value slot done' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent/green_thread_value_slot_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'value slots complete in spawn order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
