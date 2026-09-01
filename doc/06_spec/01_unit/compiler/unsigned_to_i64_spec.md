# Unsigned To I64 Specification

> Tests covering unsigned integer to_i64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsigned To I64 Specification

## Scenarios

### unsigned integer to_i64

#### preserves u8 values pushed into arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves u8 values pushed into arrays
   - Expected: xs[0].to_i64() equals `0`
   - Expected: xs[1].to_i64() equals `1`
   - Expected: xs[2].to_i64() equals `2`
   - Expected: xs[3].to_i64() equals `4`
   - Expected: xs[4].to_i64() equals `8`
   - Expected: xs[5].to_i64() equals `16`
   - Expected: xs[6].to_i64() equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves u8 values pushed into arrays")
var xs: [u8] = []
xs.push(0u8)
xs.push(1u8)
xs.push(2u8)
xs.push(4u8)
xs.push(8u8)
xs.push(16u8)
xs.push(255u8)

expect(xs[0].to_i64()).to_equal(0)
expect(xs[1].to_i64()).to_equal(1)
expect(xs[2].to_i64()).to_equal(2)
expect(xs[3].to_i64()).to_equal(4)
expect(xs[4].to_i64()).to_equal(8)
expect(xs[5].to_i64()).to_equal(16)
expect(xs[6].to_i64()).to_equal(255)
```

</details>

#### preserves TLS vector hex u8 literals

- preserves TLS vector hex u8 literals
   - Expected: salt[8].to_i64() equals `8`
   - Expected: salt[9].to_i64() equals `9`
   - Expected: salt[10].to_i64() equals `10`
   - Expected: salt[11].to_i64() equals `11`
   - Expected: salt[12].to_i64() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves TLS vector hex u8 literals")
var salt: [u8] = []
salt.push(0x00u8)
salt.push(0x01u8)
salt.push(0x02u8)
salt.push(0x03u8)
salt.push(0x04u8)
salt.push(0x05u8)
salt.push(0x06u8)
salt.push(0x07u8)
salt.push(0x08u8)
salt.push(0x09u8)
salt.push(0x0au8)
salt.push(0x0bu8)
salt.push(0x0cu8)

expect(salt[8].to_i64()).to_equal(8)
expect(salt[9].to_i64()).to_equal(9)
expect(salt[10].to_i64()).to_equal(10)
expect(salt[11].to_i64()).to_equal(11)
expect(salt[12].to_i64()).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/unsigned_to_i64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unsigned integer to_i64.
- unsigned integer to_i64

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab9c5cb9ae3b036f67b3126e0ab4ea6bcdb7b71b8987a78a426aae9bdd29b768`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab9c5cb9ae3b036f67b3126e0ab4ea6bcdb7b71b8987a78a426aae9bdd29b768`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab9c5cb9ae3b036f67b3126e0ab4ea6bcdb7b71b8987a78a426aae9bdd29b768`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/unsigned_to_i64_spec.spl
mirror: doc/06_spec/01_unit/compiler/unsigned_to_i64_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/unsigned_to_i64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/unsigned_to_i64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/unsigned_to_i64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/unsigned_to_i64_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves u8 values pushed into arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/unsigned_to_i64_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves TLS vector hex u8 literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
