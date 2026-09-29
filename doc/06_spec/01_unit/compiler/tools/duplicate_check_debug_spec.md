# Duplicate Check Debug Helpers Specification

> Tests the debug flag helpers used by the duplicate detection tool. The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide throttled progress logging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Debug Helpers Specification

Tests the debug flag helpers used by the duplicate detection tool. The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide throttled progress logging.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/duplicate_check_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the debug flag helpers used by the duplicate detection tool.
The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide
throttled progress logging.

## Key Concepts

| Concept         | Description                                      |
|-----------------|--------------------------------------------------|
| get_debug_flag  | Returns true when SIMPLE_DUP_DEBUG is "1"/"true" |
| debug_log       | Emits message only when tracing is on            |
| debug_log_progress | Throttles output to every 10th step           |

## Scenarios

### Duplicate Check Debug Flag

#### get_debug_flag returns bool

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- get_debug_flag returns bool
   - Expected: flag == true or flag == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_debug_flag returns bool")
val flag = get_debug_flag()
expect(flag == true or flag == false).to_equal(true)
```

</details>

#### get_debug_flag defaults to false when env unset

- get_debug_flag defaults to false when env unset
   - Expected: flag is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_debug_flag defaults to false when env unset")
val flag = get_debug_flag()
expect(flag).to_equal(false)
```

</details>

### Duplicate Check Debug Functions

#### init_debug does not error

- init_debug does not error
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init_debug does not error")
init_debug()
expect(get_debug_flag()).to_equal(false)
```

</details>

#### debug_log does not error when debug is off

- debug_log does not error when debug is off
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log does not error when debug is off")
debug_log("test message")
expect(get_debug_flag()).to_equal(false)
```

</details>

#### debug_log_progress does not error when debug is off

- debug_log_progress does not error when debug is off
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log_progress does not error when debug is off")
debug_log_progress(0, 10, "scanning")
debug_log_progress(5, 10, "scanning")
debug_log_progress(10, 10, "scanning")
expect(get_debug_flag()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `d85244123a0db7b72d43c9329e0b70a6137b7545742e3e91779cc1a6bf67aaa7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d85244123a0db7b72d43c9329e0b70a6137b7545742e3e91779cc1a6bf67aaa7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d85244123a0db7b72d43c9329e0b70a6137b7545742e3e91779cc1a6bf67aaa7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/tools/duplicate_check_debug_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/duplicate_check_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/tools/duplicate_check_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/duplicate_check_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/duplicate_check_debug_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_debug_flag returns bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/duplicate_check_debug_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_debug_flag defaults to false when env unset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/duplicate_check_debug_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'init_debug does not error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
