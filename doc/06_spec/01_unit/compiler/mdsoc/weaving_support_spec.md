# Weaving Support Specification

> Tests covering MDSOC weaving support types, deny advice.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Weaving Support Specification

## Scenarios

### MDSOC weaving support types

#### constructs matched advice and weaving rules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs matched advice and weaving rules
   - Expected: rule.predicate_text equals `@authenticated`
   - Expected: rule.advice_function equals `security.auth_before`
   - Expected: rule.priority equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructs matched advice and weaving rules")
val matched = MatchedAdvice(
    advice_function: "security.auth_before",
    form: AdviceForm.Before,
    priority: 10,
    specificity: 2
)
val rule = WeavingRule(
    predicate_text: "@authenticated",
    advice_function: matched.advice_function,
    form: matched.form,
    priority: matched.priority
)
expect(rule.predicate_text).to_equal("@authenticated")
expect(rule.advice_function).to_equal("security.auth_before")
expect(rule.priority).to_equal(10)
```

</details>

#### creates an empty weaving result

- creates an empty weaving result
   - Expected: result.join_points_woven equals `0`
   - Expected: result.advices_inserted equals `0`
   - Expected: result.advice_calls.len() equals `0`
   - Expected: result.diagnostics.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates an empty weaving result")
val result = weavingresult_new()
expect(result.join_points_woven).to_equal(0)
expect(result.advices_inserted).to_equal(0)
expect(result.advice_calls.len()).to_equal(0)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

### deny advice

#### returns maintenance denial for annotated join points

- returns maintenance denial for annotated join points
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns maintenance denial for annotated join points")
val ctx = JoinPointContext(
    function_name: "handle_request",
    module_path: "std.http.admin",
    signature: "fn()",
    attributes: ["peer=198.51.100.42", "deny_all"],
    effects: []
)
val result = deny_all_before(ctx)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/weaving_support_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MDSOC weaving support types, deny advice.
- MDSOC weaving support types
- deny advice

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7fb946f2368111c3d9325a787955279fb17213b327c6eea9d42cefc2ae4770f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fb946f2368111c3d9325a787955279fb17213b327c6eea9d42cefc2ae4770f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fb946f2368111c3d9325a787955279fb17213b327c6eea9d42cefc2ae4770f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mdsoc/weaving_support_spec.spl
mirror: doc/06_spec/01_unit/compiler/mdsoc/weaving_support_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mdsoc/weaving_support_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mdsoc/weaving_support_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mdsoc/weaving_support_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mdsoc/weaving_support_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs matched advice and weaving rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mdsoc/weaving_support_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates an empty weaving result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mdsoc/weaving_support_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns maintenance denial for annotated join points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
