# Test Runner Group Json Specification

> Tests covering test_file_group, test_group_summaries_json, planned marker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Group Json Specification

## Scenarios

### test_file_group

#### uses the segment after test/ as the group

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the segment after test/ as the group
   - Expected: test_file_group("test/01_unit/compiler/x_spec.spl") equals `01_unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the segment after test/ as the group")
expect(test_file_group("test/01_unit/compiler/x_spec.spl")).to_equal("01_unit")
```

</details>

#### falls back to the first segment without a test/ prefix

- falls back to the first segment without a test/ prefix
   - Expected: test_file_group("custom/lane/x_spec.spl") equals `custom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the first segment without a test/ prefix")
expect(test_file_group("custom/lane/x_spec.spl")).to_equal("custom")
```

</details>

#### returns other for a bare filename

- returns other for a bare filename
   - Expected: test_file_group("x_spec.spl") equals `other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns other for a bare filename")
expect(test_file_group("x_spec.spl")).to_equal("other")
```

</details>

### test_group_summaries_json

#### aggregates files into groups with done_pct

- aggregates files into groups with done_pct


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregates files into groups with done_pct")
val rows = [
    mk("test/01_unit/a_spec.spl", 3, 1, 0, 0),
    mk("test/01_unit/b_spec.spl", 2, 0, 1, 2),
    mk("test/02_integration/c_spec.spl", 5, 0, 0, 0)
]
val json = test_group_summaries_json(rows)
# 01_unit: passed=5 failed=1 pending=2 -> 5*100/8 = 62
expect(json).to_contain("\"name\":\"01_unit\",\"passed\":5,\"failed\":1,\"skipped\":1,\"pending\":2,\"done_pct\":62")
expect(json).to_contain("\"name\":\"02_integration\",\"passed\":5,\"failed\":0,\"skipped\":0,\"pending\":0,\"done_pct\":100")
```

</details>

#### reports done_pct 0 when a group has only skipped entries

- reports done_pct 0 when a group has only skipped entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports done_pct 0 when a group has only skipped entries")
val json = test_group_summaries_json([mk("test/03_system/only_skips_spec.spl", 0, 0, 4, 0)])
expect(json).to_contain("\"done_pct\":0")
```

</details>

#### returns an empty array for no files

- returns an empty array for no files
   - Expected: test_group_summaries_json([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty array for no files")
expect(test_group_summaries_json([])).to_equal("[]")
```

</details>

### planned marker

#### declares future work without failing

- declares future work without failing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares future work without failing")
planned("planned marker demo", "future-impl sspec reporting for dashboards")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_group_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_file_group, test_group_summaries_json, planned marker.
- test_file_group
- test_group_summaries_json
- planned marker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `ef106a1587a708d89e807751994fbe97aca4f22071e92f7477ca9f8dbb7d43a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef106a1587a708d89e807751994fbe97aca4f22071e92f7477ca9f8dbb7d43a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef106a1587a708d89e807751994fbe97aca4f22071e92f7477ca9f8dbb7d43a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/test_runner_group_json_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_group_json_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_group_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_group_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_group_json_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the segment after test/ as the group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_group_json_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the first segment without a test/ prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_group_json_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns other for a bare filename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
