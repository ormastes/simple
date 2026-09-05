# Typed Pipe Lambda Param Specification

> Tests covering typed pipe-lambda parameters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Pipe Lambda Param Specification

## Scenarios

### typed pipe-lambda parameters

#### a single typed param parses and calls correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a single typed param parses and calls correctly
   - Expected: f(5) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("a single typed param parses and calls correctly")
val f = |x: i64| x + 1
expect(f(5)).to_equal(6)
```

</details>

#### multiple typed params parse and call correctly

- multiple typed params parse and call correctly
   - Expected: g(3, 4) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("multiple typed params parse and call correctly")
val g = |x: i64, y: i64| x + y
expect(g(3, 4)).to_equal(7)
```

</details>

#### untyped params still parse correctly (no regression)

- untyped params still parse correctly (no regression)
   - Expected: h(5) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("untyped params still parse correctly (no regression)")
val h = |x| x + 1
expect(h(5)).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/typed_pipe_lambda_param_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed pipe-lambda parameters.
- typed pipe-lambda parameters

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

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e8444a1984cc2e126b5d6fdd4bafa4d39f251e694ff6a794f9f485534f7b2de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e8444a1984cc2e126b5d6fdd4bafa4d39f251e694ff6a794f9f485534f7b2de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e8444a1984cc2e126b5d6fdd4bafa4d39f251e694ff6a794f9f485534f7b2de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/language/typed_pipe_lambda_param_spec.spl
mirror: doc/06_spec/01_unit/language/typed_pipe_lambda_param_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/typed_pipe_lambda_param_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/typed_pipe_lambda_param_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/typed_pipe_lambda_param_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/typed_pipe_lambda_param_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a single typed param parses and calls correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/typed_pipe_lambda_param_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple typed params parse and call correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/typed_pipe_lambda_param_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'untyped params still parse correctly (no regression)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
