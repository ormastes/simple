# Trait Conformance Param Type Specification

> Tests covering trait conformance compares parameter types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Conformance Param Type Specification

## Scenarios

### trait conformance compares parameter types

#### flags a trait u64 parameter implemented as text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags a trait u64 parameter implemented as text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags a trait u64 parameter implemented as text")
expect(param_type_conflict(u64_ty(), text_ty())).to_be_true()
```

</details>

#### flags signedness drift on the same width

- flags signedness drift on the same width


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags signedness drift on the same width")
expect(param_type_conflict(u64_ty(), i64_ty())).to_be_true()
```

</details>

#### flags integer width drift

- flags integer width drift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags integer width drift")
expect(param_type_conflict(i64_ty(), i32_ty())).to_be_true()
```

</details>

#### flags float width drift

- flags float width drift


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags float width drift")
expect(param_type_conflict(f64_ty(), f32_ty())).to_be_true()
```

</details>

#### flags bool implemented as text

- flags bool implemented as text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags bool implemented as text")
expect(param_type_conflict(bool_ty(), text_ty())).to_be_true()
```

</details>

#### accepts identical concrete parameter types

- accepts identical concrete parameter types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts identical concrete parameter types")
expect(param_type_conflict(u64_ty(), u64_ty())).to_be_false()
expect(param_type_conflict(text_ty(), text_ty())).to_be_false()
expect(param_type_conflict(f64_ty(), f64_ty())).to_be_false()
```

</details>

#### wires the comparison into validate_methods

- wires the comparison into validate_methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires the comparison into validate_methods")
val source = file_read("src/compiler/25.traits/trait_impl.spl")
expect(source).to_contain("fn param_type_conflict(")
expect(source).to_contain("param_type_conflict(")
# the arity check must survive alongside the new type check
expect(source).to_contain("provided.params.len() != method.arity()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/traits/trait_conformance_param_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering trait conformance compares parameter types.
- trait conformance compares parameter types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `4d54b5231da2c454a8f6a584e4d3944729a87d17f5d04eebb0d23c72eac5a8e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d54b5231da2c454a8f6a584e4d3944729a87d17f5d04eebb0d23c72eac5a8e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d54b5231da2c454a8f6a584e4d3944729a87d17f5d04eebb0d23c72eac5a8e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/traits/trait_conformance_param_type_spec.spl
mirror: doc/06_spec/01_unit/compiler/traits/trait_conformance_param_type_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/traits/trait_conformance_param_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/traits/trait_conformance_param_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/traits/trait_conformance_param_type_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a trait u64 parameter implemented as text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/traits/trait_conformance_param_type_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags signedness drift on the same width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/traits/trait_conformance_param_type_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags integer width drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
