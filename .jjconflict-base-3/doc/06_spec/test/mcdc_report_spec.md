# Mcdc Report Specification

> _Per-decision MC/DC coverage report: covered/uncovered conditions and percentage._

<!-- sdn-diagram:id=mcdc_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcdc_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcdc_report_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcdc_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcdc Report Specification

## Scenarios

### MCDC report
_Per-decision MC/DC coverage report: covered/uncovered conditions and percentage._

#### reports 100% MC/DC with all conditions covered for the adequate set

- enable mcdc tag
- clear mcdc data
-  feed full set
   - Expected: rep.condition_count equals `3`
   - Expected: rep.conditions_covered equals `3`
   - Expected: rep.mcdc_percent equals `100.0`
- assert true
   - Expected: rep.covered_conditions.len() equals `3`
   - Expected: rep.uncovered_conditions.len() equals `0`
- assert contains
- assert contains
- assert contains
- disable mcdc tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_mcdc_tag()
clear_mcdc_data()
val id = register_decision("A and (B or C)", ["A", "B", "C"], "mixed", "flight.spl", 42)
_feed_full_set(id)

val rep = build_decision_report(id)
expect(rep.condition_count).to_equal(3)
expect(rep.conditions_covered).to_equal(3)
expect(rep.mcdc_percent).to_equal(100.0)
assert_true(rep.is_covered)
expect(rep.covered_conditions.len()).to_equal(3)
expect(rep.uncovered_conditions.len()).to_equal(0)
assert_contains(rep.covered_conditions, "A")
assert_contains(rep.covered_conditions, "B")
assert_contains(rep.covered_conditions, "C")
disable_mcdc_tag()
```

</details>

#### drops below 100% and names the uncovered condition when a pair is removed

- enable mcdc tag
- clear mcdc data
- record evaluation
- record evaluation
- record evaluation
   - Expected: rep.condition_count equals `3`
   - Expected: rep.conditions_covered equals `2`
- assert true
- assert false
   - Expected: rep.uncovered_conditions.len() equals `1`
- assert contains
- assert contains
- assert contains
- assert contains
- disable mcdc tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_mcdc_tag()
clear_mcdc_data()
val id = register_decision("A and (B or C)", ["A", "B", "C"], "mixed", "flight.spl", 42)
# Omit (A=T,B=F,C=T): now C has no independence pair (C only ever
# evaluated with value F), so condition index 2 becomes uncovered.
record_evaluation(id, [true, true, false], [true, true, false], true)
record_evaluation(id, [false, true, false], [true, false, false], false)
record_evaluation(id, [true, false, false], [true, true, true], false)

val rep = build_decision_report(id)
expect(rep.condition_count).to_equal(3)
expect(rep.conditions_covered).to_equal(2)
assert_true(rep.mcdc_percent < 100.0)
assert_false(rep.is_covered)
expect(rep.uncovered_conditions.len()).to_equal(1)
assert_contains(rep.uncovered_conditions, "C")
assert_contains(rep.uncovered_indices, 2)
# Covered set still names A and B.
assert_contains(rep.covered_conditions, "A")
assert_contains(rep.covered_conditions, "B")
disable_mcdc_tag()
```

</details>

#### renders a human-readable report string naming the uncovered condition

- enable mcdc tag
- clear mcdc data
- record evaluation
- record evaluation
- record evaluation
- assert contains
- assert contains
- assert contains
- disable mcdc tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_mcdc_tag()
clear_mcdc_data()
val id = register_decision("A and (B or C)", ["A", "B", "C"], "mixed", "flight.spl", 42)
record_evaluation(id, [true, true, false], [true, true, false], true)
record_evaluation(id, [false, true, false], [true, false, false], false)
record_evaluation(id, [true, false, false], [true, true, true], false)

val text_report = format_decision_report(id)
assert_contains(text_report, "A and (B or C)")
assert_contains(text_report, "Uncovered")
assert_contains(text_report, "C")
disable_mcdc_tag()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `src/lib/nogc_sync_mut/test/mcdc_report_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCDC report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
