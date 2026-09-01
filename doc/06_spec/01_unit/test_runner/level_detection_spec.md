# Level Detection Specification

> Tests covering strip_order_prefix, test_level_of_path — maintained numbered tree, test_level_of_path — legacy bare mirror, test_level_of_path — negative cases, test_level_of_path — windows separators, path_has_level_segment, test_level_matches — the filter the CLI applies.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Level Detection Specification

## Scenarios

### strip_order_prefix

#### strips a two-digit ordering prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- strips a two-digit ordering prefix
   - Expected: strip_order_prefix("01_unit") equals `unit`
   - Expected: strip_order_prefix("02_integration") equals `integration`
   - Expected: strip_order_prefix("03_system") equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a two-digit ordering prefix")
expect(strip_order_prefix("01_unit")).to_equal("unit")
expect(strip_order_prefix("02_integration")).to_equal("integration")
expect(strip_order_prefix("03_system")).to_equal("system")
```

</details>

#### leaves segments without an NN_ prefix untouched

- leaves segments without an NN_ prefix untouched
   - Expected: strip_order_prefix("unit") equals `unit`
   - Expected: strip_order_prefix("1_unit") equals `1_unit`
   - Expected: strip_order_prefix("_unit") equals `_unit`
   - Expected: strip_order_prefix("ab_unit") equals `ab_unit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves segments without an NN_ prefix untouched")
expect(strip_order_prefix("unit")).to_equal("unit")
expect(strip_order_prefix("1_unit")).to_equal("1_unit")
expect(strip_order_prefix("_unit")).to_equal("_unit")
expect(strip_order_prefix("ab_unit")).to_equal("ab_unit")
```

</details>

### test_level_of_path — maintained numbered tree

#### classifies 01_unit as unit

- classifies 01_unit as unit
   - Expected: test_level_of_path("test/01_unit/test_runner/mode_filter_spec.spl") equals `TEST_LEVEL_UNIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies 01_unit as unit")
expect(test_level_of_path("test/01_unit/test_runner/mode_filter_spec.spl")).to_equal(TEST_LEVEL_UNIT)
```

</details>

#### classifies 02_integration as integration

- classifies 02_integration as integration
   - Expected: test_level_of_path("test/02_integration/compiler/pipeline_spec.spl") equals `TEST_LEVEL_INTEGRATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies 02_integration as integration")
expect(test_level_of_path("test/02_integration/compiler/pipeline_spec.spl")).to_equal(TEST_LEVEL_INTEGRATION)
```

</details>

#### classifies 03_system as system

- classifies 03_system as system
   - Expected: test_level_of_path("test/03_system/os/boot_spec.spl") equals `TEST_LEVEL_SYSTEM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies 03_system as system")
expect(test_level_of_path("test/03_system/os/boot_spec.spl")).to_equal(TEST_LEVEL_SYSTEM)
```

</details>

### test_level_of_path — legacy bare mirror

#### classifies unit as unit

- classifies unit as unit
   - Expected: test_level_of_path("test/unit/test_runner/mode_filter_spec.spl") equals `TEST_LEVEL_UNIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies unit as unit")
expect(test_level_of_path("test/unit/test_runner/mode_filter_spec.spl")).to_equal(TEST_LEVEL_UNIT)
```

</details>

#### classifies integration as integration

- classifies integration as integration
   - Expected: test_level_of_path("test/integration/compiler/pipeline_spec.spl") equals `TEST_LEVEL_INTEGRATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies integration as integration")
expect(test_level_of_path("test/integration/compiler/pipeline_spec.spl")).to_equal(TEST_LEVEL_INTEGRATION)
```

</details>

#### classifies system and feature as system

- classifies system and feature as system
   - Expected: test_level_of_path("test/system/os/boot_spec.spl") equals `TEST_LEVEL_SYSTEM`
   - Expected: test_level_of_path("test/feature/wm/glass_spec.spl") equals `TEST_LEVEL_SYSTEM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies system and feature as system")
expect(test_level_of_path("test/system/os/boot_spec.spl")).to_equal(TEST_LEVEL_SYSTEM)
expect(test_level_of_path("test/feature/wm/glass_spec.spl")).to_equal(TEST_LEVEL_SYSTEM)
```

</details>

#### classifies shared as unit

- classifies shared as unit
   - Expected: test_level_of_path("test/shared/helpers_spec.spl") equals `TEST_LEVEL_UNIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies shared as unit")
expect(test_level_of_path("test/shared/helpers_spec.spl")).to_equal(TEST_LEVEL_UNIT)
```

</details>

### test_level_of_path — negative cases

#### does not treat a substring inside a longer word as a level segment

- does not treat a substring inside a longer word as a level segment
   - Expected: test_level_of_path("test/09_baselines/opportunity/report_spec.spl") equals `TEST_LEVEL_NONE`
   - Expected: test_level_of_path("test/app/community/feed_spec.spl") equals `TEST_LEVEL_NONE`
   - Expected: test_level_of_path("test/app/ecosystem/graph_spec.spl") equals `TEST_LEVEL_NONE`
   - Expected: test_level_of_path("test/app/disintegration/decay_spec.spl") equals `TEST_LEVEL_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat a substring inside a longer word as a level segment")
# "opportunity" and "community" both CONTAIN "unit" — they must not classify.
expect(test_level_of_path("test/09_baselines/opportunity/report_spec.spl")).to_equal(TEST_LEVEL_NONE)
expect(test_level_of_path("test/app/community/feed_spec.spl")).to_equal(TEST_LEVEL_NONE)
# "ecosystem" contains "system"; "disintegration" contains "integration".
expect(test_level_of_path("test/app/ecosystem/graph_spec.spl")).to_equal(TEST_LEVEL_NONE)
expect(test_level_of_path("test/app/disintegration/decay_spec.spl")).to_equal(TEST_LEVEL_NONE)
```

</details>

#### leaves unnumbered non-level trees unclassified in both forms

- leaves unnumbered non-level trees unclassified in both forms
   - Expected: test_level_of_path("test/04_smoke/cli_spec.spl") equals `TEST_LEVEL_NONE`
   - Expected: test_level_of_path("test/smoke/cli_spec.spl") equals `TEST_LEVEL_NONE`
   - Expected: test_level_of_path("test/05_perf/test_runner_benchmark_spec.spl") equals `TEST_LEVEL_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves unnumbered non-level trees unclassified in both forms")
expect(test_level_of_path("test/04_smoke/cli_spec.spl")).to_equal(TEST_LEVEL_NONE)
expect(test_level_of_path("test/smoke/cli_spec.spl")).to_equal(TEST_LEVEL_NONE)
expect(test_level_of_path("test/05_perf/test_runner_benchmark_spec.spl")).to_equal(TEST_LEVEL_NONE)
```

</details>

#### does not classify a file whose basename merely mentions a level

- does not classify a file whose basename merely mentions a level
   - Expected: test_level_of_path("test/fixtures/unit_helper_spec.spl") equals `TEST_LEVEL_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not classify a file whose basename merely mentions a level")
expect(test_level_of_path("test/fixtures/unit_helper_spec.spl")).to_equal(TEST_LEVEL_NONE)
```

</details>

### test_level_of_path — windows separators

#### normalizes backslashes before segmenting

- normalizes backslashes before segmenting
   - Expected: test_level_of_path("test\\01_unit\\app\\cli_spec.spl") equals `TEST_LEVEL_UNIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes backslashes before segmenting")
expect(test_level_of_path("test\\01_unit\\app\\cli_spec.spl")).to_equal(TEST_LEVEL_UNIT)
```

</details>

### path_has_level_segment

#### matches whole segments in both hierarchies

- matches whole segments in both hierarchies
   - Expected: path_has_level_segment("test/01_unit/a_spec.spl", "unit") is true
   - Expected: path_has_level_segment("test/unit/a_spec.spl", "unit") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches whole segments in both hierarchies")
expect(path_has_level_segment("test/01_unit/a_spec.spl", "unit")).to_equal(true)
expect(path_has_level_segment("test/unit/a_spec.spl", "unit")).to_equal(true)
```

</details>

#### rejects a substring inside a longer segment

- rejects a substring inside a longer segment
   - Expected: path_has_level_segment("test/opportunity/a_spec.spl", "unit") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a substring inside a longer segment")
expect(path_has_level_segment("test/opportunity/a_spec.spl", "unit")).to_equal(false)
```

</details>

### test_level_matches — the filter the CLI applies

#### selects numbered-tree specs for --unit (the regression)

- selects numbered-tree specs for --unit (the regression)
   - Expected: test_level_matches("test/01_unit/app/cli_spec.spl", TEST_LEVEL_UNIT) is true
   - Expected: test_level_matches("test/01_unit/app/cli_spec.spl", TEST_LEVEL_SYSTEM) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects numbered-tree specs for --unit (the regression)")
expect(test_level_matches("test/01_unit/app/cli_spec.spl", TEST_LEVEL_UNIT)).to_equal(true)
expect(test_level_matches("test/01_unit/app/cli_spec.spl", TEST_LEVEL_SYSTEM)).to_equal(false)
```

</details>

#### still selects mirror specs for --unit

- still selects mirror specs for --unit
   - Expected: test_level_matches("test/unit/app/cli_spec.spl", TEST_LEVEL_UNIT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still selects mirror specs for --unit")
expect(test_level_matches("test/unit/app/cli_spec.spl", TEST_LEVEL_UNIT)).to_equal(true)
```

</details>

#### selects numbered-tree specs for --integration and --system

- selects numbered-tree specs for --integration and --system
   - Expected: test_level_matches("test/02_integration/db/tx_spec.spl", TEST_LEVEL_INTEGRATION) is true
   - Expected: test_level_matches("test/03_system/os/boot_spec.spl", TEST_LEVEL_SYSTEM) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects numbered-tree specs for --integration and --system")
expect(test_level_matches("test/02_integration/db/tx_spec.spl", TEST_LEVEL_INTEGRATION)).to_equal(true)
expect(test_level_matches("test/03_system/os/boot_spec.spl", TEST_LEVEL_SYSTEM)).to_equal(true)
```

</details>

#### treats level code 0 as all-levels

- treats level code 0 as all-levels
   - Expected: test_level_matches("test/04_smoke/cli_spec.spl", TEST_LEVEL_NONE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats level code 0 as all-levels")
expect(test_level_matches("test/04_smoke/cli_spec.spl", TEST_LEVEL_NONE)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/level_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strip_order_prefix, test_level_of_path — maintained numbered tree, test_level_of_path — legacy bare mirror, test_level_of_path — negative cases, test_level_of_path — windows separators, path_has_level_segment, test_level_matches — the filter the CLI applies.
- strip_order_prefix
- test_level_of_path — maintained numbered tree
- test_level_of_path — legacy bare mirror
- test_level_of_path — negative cases
- test_level_of_path — windows separators
- path_has_level_segment
- test_level_matches — the filter the CLI applies

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36a31f41183016e3477411cba8be2ed56e3caf13ce6733deb937ca6a6c35e285`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36a31f41183016e3477411cba8be2ed56e3caf13ce6733deb937ca6a6c35e285`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36a31f41183016e3477411cba8be2ed56e3caf13ce6733deb937ca6a6c35e285`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/test_runner/level_detection_spec.spl
mirror: doc/06_spec/01_unit/test_runner/level_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/level_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/level_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/level_detection_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips a two-digit ordering prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/level_detection_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves segments without an NN_ prefix untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/level_detection_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies 01_unit as unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
