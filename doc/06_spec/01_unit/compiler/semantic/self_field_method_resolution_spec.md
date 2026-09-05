# Self Field Method Resolution Specification

> Tests covering self.field.method() resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Self Field Method Resolution Specification

## Scenarios

### self.field.method() resolution

#### dispatches through struct field to correct method

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches through struct field to correct method
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dispatches through struct field to correct method")
val outer_val = make_outer(42)
val result = outer_val.trigger()
expect(result).to_equal(42)
```

</details>

#### two-level chained field method call returns correct value

- two-level chained field method call returns correct value
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two-level chained field method call returns correct value")
val outer_val = make_outer(7)
val result = outer_val.trigger()
expect(result).to_equal(7)
```

</details>

#### field method result used in arithmetic

- field method result used in arithmetic
   - Expected: doubled equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("field method result used in arithmetic")
val outer_val = make_outer(10)
val doubled = outer_val.trigger() * 2
expect(doubled).to_equal(20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering self.field.method() resolution.
- self.field.method() resolution

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

- Canonical SPipe generation for source `3098f298493ca1cafabbe1efb102bfdac259d6eb411512d3da00183f087609b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3098f298493ca1cafabbe1efb102bfdac259d6eb411512d3da00183f087609b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3098f298493ca1cafabbe1efb102bfdac259d6eb411512d3da00183f087609b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantic/self_field_method_resolution_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantic/self_field_method_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantic/self_field_method_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches through struct field to correct method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two-level chained field method call returns correct value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantic/self_field_method_resolution_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'field method result used in arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
