# Hm Source Diagnostics Specification

> Tests covering HM source diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hm Source Diagnostics Specification

## Scenarios

### HM source diagnostics

#### accepts expression-bodied non-unit returns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts expression-bodied non-unit returns
   - Expected: hm_diagnostic_count("fn answer() -> i64:\n    42\n", "hm_valid_return.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts expression-bodied non-unit returns")
expect(hm_diagnostic_count("fn answer() -> i64:\n    42\n", "hm_valid_return.spl")).to_equal(0)
```

</details>

#### rejects mismatched expression-bodied returns

- rejects mismatched expression-bodied returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects mismatched expression-bodied returns")
expect(hm_diagnostic_count("fn answer() -> bool:\n    42\n", "hm_invalid_return.spl")).to_be_greater_than(0)
```

</details>

#### discards trailing values in unit functions

- discards trailing values in unit functions
   - Expected: hm_diagnostic_count("fn main():\n    42\n", "hm_unit_return.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("discards trailing values in unit functions")
expect(hm_diagnostic_count("fn main():\n    42\n", "hm_unit_return.spl")).to_equal(0)
```

</details>

#### rejects annotated local mismatches

- rejects annotated local mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects annotated local mismatches")
expect(hm_diagnostic_count("fn main():\n    val x: i64 = \"text\"\n", "hm_invalid_local.spl")).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HM source diagnostics.
- HM source diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `10a8b82017b43b091a2e99eb2af4ccf39799025881cb9064b90c5063dafd5c74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10a8b82017b43b091a2e99eb2af4ccf39799025881cb9064b90c5063dafd5c74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10a8b82017b43b091a2e99eb2af4ccf39799025881cb9064b90c5063dafd5c74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl
mirror: doc/06_spec/01_unit/compiler/type_inference/hm_source_diagnostics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/type_inference/hm_source_diagnostics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/type_inference/hm_source_diagnostics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts expression-bodied non-unit returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects mismatched expression-bodied returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/type_inference/hm_source_diagnostics_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discards trailing values in unit functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
