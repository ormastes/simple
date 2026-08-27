# Lazy Numeric Guard Specification

> Tests covering nogc_async_mut mcp lazy numeric guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Numeric Guard Specification

## Scenarios

### nogc_async_mut mcp lazy numeric guards

#### guards debug log query numeric filters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards debug log query numeric filters
   - Expected: _debug_log_int_or_zero("42") equals `42`
   - Expected: _debug_log_int_or_zero(" 7 ") equals `7`
   - Expected: _debug_log_int_or_zero("") equals `0`
   - Expected: _debug_log_int_or_zero("12x") equals `0`
   - Expected: _debug_log_int_or_zero("-3") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards debug log query numeric filters")
# oracle: digit-only input parses exactly; everything else clamps to 0
expect(_debug_log_int_or_zero("42")).to_equal(42)
expect(_debug_log_int_or_zero(" 7 ")).to_equal(7)
expect(_debug_log_int_or_zero("")).to_equal(0)
expect(_debug_log_int_or_zero("12x")).to_equal(0)
expect(_debug_log_int_or_zero("-3")).to_equal(0)
```

</details>

#### guards terminal numeric params

- guards terminal numeric params
   - Expected: _term_extract_int_param("{}", "lines") equals `0`
   - Expected: _term_extract_int_param("{\"lines\":\"9x9\"}", "lines") equals `0`
   - Expected: _term_extract_int_param("", "lines") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards terminal numeric params")
# oracle: missing or non-numeric terminal params must fail closed to 0
expect(_term_extract_int_param("{}", "lines")).to_equal(0)
expect(_term_extract_int_param("{\"lines\":\"9x9\"}", "lines")).to_equal(0)
expect(_term_extract_int_param("", "lines")).to_equal(0)
```

</details>

#### guards outline line selectors

- guards outline line selectors
   - Expected: outline_line_selector_or_zero("line:12") equals `12`
   - Expected: outline_line_selector_or_zero("line:") equals `0`
   - Expected: outline_line_selector_or_zero("line:1x") equals `0`
   - Expected: outline_line_selector_or_zero("12") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards outline line selectors")
# oracle: well-formed line: selectors parse exactly; malformed ones clamp to 0
expect(outline_line_selector_or_zero("line:12")).to_equal(12)
expect(outline_line_selector_or_zero("line:")).to_equal(0)
expect(outline_line_selector_or_zero("line:1x")).to_equal(0)
expect(outline_line_selector_or_zero("12")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut mcp lazy numeric guards.
- nogc_async_mut mcp lazy numeric guards

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

- Canonical SPipe generation for source `d451562a61bb1dfaa892c01aa171b3150e84140558a679e1f0e1ce7299a4b2c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d451562a61bb1dfaa892c01aa171b3150e84140558a679e1f0e1ce7299a4b2c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d451562a61bb1dfaa892c01aa171b3150e84140558a679e1f0e1ce7299a4b2c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards debug log query numeric filters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards terminal numeric params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards outline line selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
