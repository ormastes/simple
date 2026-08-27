# Formatter Comprehensive Specification

> Tests covering Formatter Comprehensive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Comprehensive Specification

## Scenarios

### Formatter Comprehensive

#### keeps long line breaking and CLI formatting helpers available

- keeps long line breaking and CLI formatting helpers available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps long line breaking and CLI formatting helpers available")
val source = formatter_source()

expect(source).to_contain("fn break_long_line(line: String, base_indent: Int) -> [String]")
expect(source).to_contain("fn is_method_chain(line: String) -> Bool")
expect(source).to_contain("fn break_method_chain(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn break_function_signature(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn break_function_call(line: String, indent_str: String, continuation_str: String) -> [String]")
expect(source).to_contain("fn format_file_inplace(path: String) -> Result<String, String>")
expect(source).to_contain("fn check_formatting(path: String) -> Result<Bool, String>")
```

</details>

#### keeps in-place formatting on the canonical atomic writer

- keeps in-place formatting on the canonical atomic writer
   - Expected: source does not contain `if not file_write(path, content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps in-place formatting on the canonical atomic writer")
val source = formatter_source()

expect(source).to_contain("if not file_atomic_write(path, content)")
expect(source.contains("if not file_write(path, content)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter_comprehensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Formatter Comprehensive.
- Formatter Comprehensive

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8cba3da64db8e76d44dbe6ae023c8f3b8a22e64b279dd289badb15e800105419`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cba3da64db8e76d44dbe6ae023c8f3b8a22e64b279dd289badb15e800105419`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cba3da64db8e76d44dbe6ae023c8f3b8a22e64b279dd289badb15e800105419`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/formatter_comprehensive_spec.spl
mirror: doc/06_spec/01_unit/app/formatter_comprehensive_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/app/formatter_comprehensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/formatter_comprehensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/formatter_comprehensive_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/formatter_comprehensive_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/formatter_comprehensive_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps long line breaking and CLI formatting helpers available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/formatter_comprehensive_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps in-place formatting on the canonical atomic writer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
