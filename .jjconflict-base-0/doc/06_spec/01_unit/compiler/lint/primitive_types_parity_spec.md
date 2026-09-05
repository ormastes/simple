# Primitive Types Parity Specification

> Tests covering canonical primitive type table.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive Types Parity Specification

## Scenarios

### canonical primitive type table

#### expected set parity (mirrors Rust seed rules.rs PRIMITIVE_TYPES)

#### matches the expected 11-entry set exactly

- matches the expected 11-entry set exactly
   - Expected: canonical.len() equals `11`
   - Expected: canonical[i] equals `expected[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches the expected 11-entry set exactly")
val expected = ["i8", "i16", "i32", "i64",
                "u8", "u16", "u32", "u64",
                "f32", "f64", "bool"]
val canonical = bare_primitive_types()
expect(canonical.len()).to_equal(11)
var i = 0
while i < expected.len():
    expect(canonical[i]).to_equal(expected[i])
    i = i + 1
```

</details>

#### includes bool

- includes bool
   - Expected: is_bare_primitive_name("bool") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("includes bool")
expect(is_bare_primitive_name("bool")).to_equal(true)
```

</details>

#### rejects non-primitives and text types

- rejects non-primitives and text types
   - Expected: is_bare_primitive_name("text") is false
   - Expected: is_bare_primitive_name("str") is false
   - Expected: is_bare_primitive_name("MyType") is false
   - Expected: is_bare_primitive_name("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects non-primitives and text types")
expect(is_bare_primitive_name("text")).to_equal(false)
expect(is_bare_primitive_name("str")).to_equal(false)
expect(is_bare_primitive_name("MyType")).to_equal(false)
expect(is_bare_primitive_name("")).to_equal(false)
```

</details>

#### consumer parity

#### fix-rule primitive_api_types() equals the canonical table

- fix-rule primitive_api_types() equals the canonical table
   - Expected: ts.len() equals `canonical.len()`
   - Expected: ts[i] equals `canonical[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fix-rule primitive_api_types() equals the canonical table")
val ts = primitive_api_types()
val canonical = bare_primitive_types()
expect(ts.len()).to_equal(canonical.len())
var i = 0
while i < ts.len():
    expect(ts[i]).to_equal(canonical[i])
    i = i + 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/primitive_types_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering canonical primitive type table.
- canonical primitive type table

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

- Canonical SPipe generation for source `ca7f8f9132969ee6e43f7c1ea28c32913542a39c9208a8f5b35049f65a39759f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca7f8f9132969ee6e43f7c1ea28c32913542a39c9208a8f5b35049f65a39759f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca7f8f9132969ee6e43f7c1ea28c32913542a39c9208a8f5b35049f65a39759f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/lint/primitive_types_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/primitive_types_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/primitive_types_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/primitive_types_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/primitive_types_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/primitive_types_parity_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the expected 11-entry set exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/primitive_types_parity_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/primitive_types_parity_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-primitives and text types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
