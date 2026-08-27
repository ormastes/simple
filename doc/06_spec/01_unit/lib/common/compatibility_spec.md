# Compatibility Specification

> Tests covering SDN Rust Compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compatibility Specification

## Scenarios

### SDN Rust Compatibility

#### primitives

#### matches Rust for integers

- matches Rust for integers
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for integers")
val result = parse("pos: 42\nneg: -17\nzero: 0\nlarge: 999999")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for floats

- matches Rust for floats
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for floats")
val result = parse("pi: 3.14159\nneg: -2.718\nzero: 0.0")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for strings

- matches Rust for strings
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for strings")
val result = parse("bare: hello")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for booleans

- matches Rust for booleans
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for booleans")
val result = parse("yes: true\nno: false")
expect(result).to_equal(nil)
```

</details>

#### collections

#### matches Rust for inline arrays

- matches Rust for inline arrays
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for inline arrays")
val result = parse("items = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for block collections

- matches Rust for block collections
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Rust for block collections")
val result = parse("config:\n    host: localhost\n    port: 8080")
expect(result).to_equal(nil)
```

</details>

#### serialization

#### produces compatible SDN output

- produces compatible SDN output
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces compatible SDN output")
val result = parse("name: Alice\nage: 30\nactive: true")
expect(result).to_equal(nil)
```

</details>

#### produces compatible output for arrays

- produces compatible output for arrays
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces compatible output for arrays")
val result = parse("items = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compatibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN Rust Compatibility.
- SDN Rust Compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `7a8652160e111e5c2a896607933931bdb73785e8fa31e414b16b2ba6a5dc2684`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a8652160e111e5c2a896607933931bdb73785e8fa31e414b16b2ba6a5dc2684`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a8652160e111e5c2a896607933931bdb73785e8fa31e414b16b2ba6a5dc2684`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compatibility_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compatibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compatibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compatibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compatibility_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches Rust for integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compatibility_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches Rust for floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compatibility_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches Rust for strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
