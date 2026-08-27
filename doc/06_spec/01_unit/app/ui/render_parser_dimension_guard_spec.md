# Render Parser Dimension Guard Specification

> Tests covering render parser dimension guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Parser Dimension Guard Specification

## Scenarios

### render parser dimension guard

#### guards malformed CLI dimensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards malformed CLI dimensions
   - Expected: source does not contain `args[i + 1].to_int()`
   - Expected: source does not contain `arg[8:].to_int()`
   - Expected: source does not contain `arg[9:].to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards malformed CLI dimensions")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = rt_file_read_text("src/app/ui.render/parser.spl") ?? ""

expect(source).to_contain("fn parse_dimension_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("for ch in trimmed:")
expect(source).to_contain("if ch < \"0\" or ch > \"9\":")
expect(source).to_contain("val parsed = trimmed.to_int() ?? default_value")
expect(source).to_contain("config.width = parse_dimension_or_default(args[i + 1], config.width)")
expect(source).to_contain("config.width = parse_dimension_or_default(arg[8:], config.width)")
expect(source).to_contain("config.height = parse_dimension_or_default(args[i + 1], config.height)")
expect(source).to_contain("config.height = parse_dimension_or_default(arg[9:], config.height)")
expect(source.contains("args[i + 1].to_int()")).to_equal(false)
expect(source.contains("arg[8:].to_int()")).to_equal(false)
expect(source.contains("arg[9:].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/render_parser_dimension_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering render parser dimension guard.
- render parser dimension guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d87fd54ed88505f7fe764fe728722a95d8fb12f4385fb9f5e560923e452657bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d87fd54ed88505f7fe764fe728722a95d8fb12f4385fb9f5e560923e452657bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d87fd54ed88505f7fe764fe728722a95d8fb12f4385fb9f5e560923e452657bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/render_parser_dimension_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/render_parser_dimension_guard_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/render_parser_dimension_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/render_parser_dimension_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/render_parser_dimension_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
