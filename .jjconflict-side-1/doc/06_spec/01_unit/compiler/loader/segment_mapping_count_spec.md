# Segment Mapping Count Specification

> Tests covering loader maps one region per segment, receipt proves the mapping count against the plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Segment Mapping Count Specification

## Scenarios

### loader maps one region per segment

#### makes exactly one mapping per segment for 2 segments x 3 symbols

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- makes exactly one mapping per segment for 2 segments x 3 symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes exactly one mapping per segment for 2 segments x 3 symbols")
val mapper = map_case("mod_small", 2, 3)
val stats = mapper.stats()
assert_eq(stats.segment_count, 2)
assert_eq(stats.mapping_calls, 2)
assert_eq(stats.symbol_count, 6)
```

</details>

#### keeps the mapping count flat when symbol count grows 10x

- keeps the mapping count flat when symbol count grows 10x


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the mapping count flat when symbol count grows 10x")
val small = map_case("mod_a", 2, 3).stats()
val large = map_case("mod_b", 2, 30).stats()
# Symbols grew 10x ...
assert_eq(small.symbol_count, 6)
assert_eq(large.symbol_count, 60)
# ... mappings did not move at all. This is the whole point: under
# the per-symbol loader these two numbers were 6 and 60.
assert_eq(small.mapping_calls, large.mapping_calls)
assert_eq(large.mapping_calls, 2)
assert_eq(large.segment_count, 2)
```

</details>

#### scales mappings with segments, not symbols

- scales mappings with segments, not symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales mappings with segments, not symbols")
val one_seg = map_case("mod_c", 1, 40).stats()
val four_seg = map_case("mod_d", 4, 1).stats()
assert_eq(one_seg.mapping_calls, 1)
assert_eq(four_seg.mapping_calls, 4)
assert_true(one_seg.symbol_count > four_seg.symbol_count)
```

</details>

#### flips protection once per segment, not once per symbol

- flips protection once per segment, not once per symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flips protection once per segment, not once per symbol")
val stats = map_case("mod_prot", 2, 25).stats()
# One RW->RX transition per mapped segment.
assert_eq(stats.protection_transitions, 2)
```

</details>

### receipt proves the mapping count against the plan

#### checks GREEN when observed segment_count equals the plan

- checks GREEN when observed segment_count equals the plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks GREEN when observed segment_count equals the plan")
var mapper = map_case("mod_receipt", 3, 12)
val stats = mapper.stats()
val plan = segment_load_plan("fixture.smf", "host", 3, stats.bytes_mapped, 0, 0, 36)
val receipt = segment_load_receipt(plan, "digest", stats, stats.bytes_mapped, 0, 0, "ok", "")
assert_eq(receipt.segment_count, 3)
val verdict = load_receipt_check_against_plan(plan, receipt)
assert_true(verdict.ok)
```

</details>

#### checks RED when the load maps per symbol instead of per segment

- checks RED when the load maps per symbol instead of per segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks RED when the load maps per symbol instead of per segment")
# NEGATIVE CONTROL: a plan that intends 3 segment mappings, and a
# receipt reporting one mapping per symbol (36). The check must
# refuse it and name segment_count -- otherwise this whole spec
# could pass while the loader regressed.
var mapper = map_case("mod_regress", 3, 12)
val stats = mapper.stats()
val plan = segment_load_plan("fixture.smf", "host", 3, stats.bytes_mapped, 0, 0, 36)
val per_symbol = segment_load_receipt(plan, "digest", stats, stats.bytes_mapped, 0, 0, "ok", "")
var regressed = per_symbol
regressed.segment_count = 36
val verdict = load_receipt_check_against_plan(plan, regressed)
assert_true(not verdict.ok)
assert_true(verdict.mismatch.contains("segment_count"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/segment_mapping_count_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering loader maps one region per segment, receipt proves the mapping count against the plan.
- loader maps one region per segment
- receipt proves the mapping count against the plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ba908c59bf7e09e4ea03f0e83bbe14b2ef29a8881b52d8e89a98749433cb1fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ba908c59bf7e09e4ea03f0e83bbe14b2ef29a8881b52d8e89a98749433cb1fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ba908c59bf7e09e4ea03f0e83bbe14b2ef29a8881b52d8e89a98749433cb1fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/segment_mapping_count_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/segment_mapping_count_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/segment_mapping_count_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/segment_mapping_count_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/segment_mapping_count_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes exactly one mapping per segment for 2 segments x 3 symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/segment_mapping_count_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the mapping count flat when symbol count grows 10x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/segment_mapping_count_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scales mappings with segments, not symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
