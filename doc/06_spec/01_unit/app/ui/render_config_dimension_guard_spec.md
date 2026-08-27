# Render Config Dimension Guard Specification

> Tests covering render config dimension guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Config Dimension Guard Specification

## Scenarios

### render config dimension guard

#### guards malformed environment dimensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards malformed environment dimensions
   - Expected: source does not contain `result.width = env_width.to_int()`
   - Expected: source does not contain `result.height = env_height.to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards malformed environment dimensions")
val source = rt_file_read_text("src/app/ui.render/config.spl") ?? ""

expect(source).to_contain("fn parse_env_dimension_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("for ch in trimmed:")
expect(source).to_contain("if ch < \"0\" or ch > \"9\":")
expect(source).to_contain("val parsed = trimmed.to_int() ?? default_value")
expect(source).to_contain("result.width = parse_env_dimension_or_default(env_width, result.width)")
expect(source).to_contain("result.height = parse_env_dimension_or_default(env_height, result.height)")
expect(source.contains("result.width = env_width.to_int()")).to_equal(false)
expect(source.contains("result.height = env_height.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/render_config_dimension_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering render config dimension guard.
- render config dimension guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f5eafccd391cf155cd91f879c78615b676ddbf9a401ded786ce2cce0c9b107d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f5eafccd391cf155cd91f879c78615b676ddbf9a401ded786ce2cce0c9b107d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f5eafccd391cf155cd91f879c78615b676ddbf9a401ded786ce2cce0c9b107d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/render_config_dimension_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/render_config_dimension_guard_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/render_config_dimension_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/render_config_dimension_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/render_config_dimension_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui/render_config_dimension_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/ui/render_config_dimension_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards malformed environment dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
