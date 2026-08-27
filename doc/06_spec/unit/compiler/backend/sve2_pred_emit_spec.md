# Sve2 Pred Emit Specification

> Tests covering SVE2 predicate emit golden bytes, PTRUE, PFALSE, WHILELT, WHILELE, AND predicate, ORR predicate, EOR predicate, NOT predicate, BRKA, PNEXT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Pred Emit Specification

## Scenarios

### SVE2 predicate emit golden bytes

### PTRUE

#### ptrue_s pd=0

- ptrue_s pd=0
   - Expected: b.length equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0x18`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ptrue_s pd=0")
val b = emit_ptrue_s(0)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

#### ptrue_s pd=3

- ptrue_s pd=3
   - Expected: b[0] equals `0x03`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0x18`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ptrue_s pd=3")
val b = emit_ptrue_s(3)
expect(b[0]).to_equal(0x03)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

### PFALSE

#### pfalse pd=0

- pfalse pd=0
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x18`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pfalse pd=0")
val b = emit_pfalse(0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

#### pfalse pd=7

- pfalse pd=7
   - Expected: b[0] equals `0x07`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x18`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pfalse pd=7")
val b = emit_pfalse(7)
expect(b[0]).to_equal(0x07)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

### WHILELT

#### whilelt_s pd=0 rn=0 rm=0

- whilelt_s pd=0 rn=0 rm=0
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whilelt_s pd=0 rn=0 rm=0")
val b = emit_whilelt_s(0, 0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x25)
```

</details>

#### whilelt_s pd=1 rn=2 rm=3

- whilelt_s pd=1 rn=2 rm=3
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whilelt_s pd=1 rn=2 rm=3")
val b = emit_whilelt_s(1, 2, 3)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x25)
```

</details>

### WHILELE

#### whilele_s pd=2 rn=5 rm=10

- whilele_s pd=2 rn=5 rm=10
   - Expected: b[0] equals `0xA2`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xAA`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whilele_s pd=2 rn=5 rm=10")
val b = emit_whilele_s(2, 5, 10)
expect(b[0]).to_equal(0xA2)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xAA)
expect(b[3]).to_equal(0x25)
```

</details>

### AND predicate

#### and_pred pd=0 pg=1 pn=2 pm=3

- and_pred pd=0 pg=1 pn=2 pm=3
   - Expected: b[0] equals `0x40`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0x03`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and_pred pd=0 pg=1 pn=2 pm=3")
val b = emit_and_pred(0, 1, 2, 3)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0x03)
expect(b[3]).to_equal(0x25)
```

</details>

#### and_pred pd=5 pg=7 pn=3 pm=15

- and_pred pd=5 pg=7 pn=3 pm=15
   - Expected: b[0] equals `0x65`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0x0F`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and_pred pd=5 pg=7 pn=3 pm=15")
val b = emit_and_pred(5, 7, 3, 15)
expect(b[0]).to_equal(0x65)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0x0F)
expect(b[3]).to_equal(0x25)
```

</details>

### ORR predicate

#### orr_pred pd=0 pg=0 pn=0 pm=0

- orr_pred pd=0 pg=0 pn=0 pm=0
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orr_pred pd=0 pg=0 pn=0 pm=0")
val b = emit_orr_pred(0, 0, 0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x25)
```

</details>

#### orr_pred pd=1 pg=2 pn=3 pm=4

- orr_pred pd=1 pg=2 pn=3 pm=4
   - Expected: b[0] equals `0x61`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0x84`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orr_pred pd=1 pg=2 pn=3 pm=4")
val b = emit_orr_pred(1, 2, 3, 4)
expect(b[0]).to_equal(0x61)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x84)
expect(b[3]).to_equal(0x25)
```

</details>

### EOR predicate

#### eor_pred pd=0 pg=1 pn=2 pm=3

- eor_pred pd=0 pg=1 pn=2 pm=3
   - Expected: b[0] equals `0x40`
   - Expected: b[1] equals `0x46`
   - Expected: b[2] equals `0x03`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eor_pred pd=0 pg=1 pn=2 pm=3")
val b = emit_eor_pred(0, 1, 2, 3)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x46)
expect(b[2]).to_equal(0x03)
expect(b[3]).to_equal(0x25)
```

</details>

### NOT predicate

#### not_pred pd=0 pg=0 pn=0

- not_pred pd=0 pg=0 pn=0
   - Expected: b[0] equals `0x10`
   - Expected: b[1] equals `0x42`
   - Expected: b[2] equals `0x00`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not_pred pd=0 pg=0 pn=0")
val b = emit_not_pred(0, 0, 0)
expect(b[0]).to_equal(0x10)
expect(b[1]).to_equal(0x42)
expect(b[2]).to_equal(0x00)
expect(b[3]).to_equal(0x25)
```

</details>

#### not_pred pd=1 pg=2 pn=3

- not_pred pd=1 pg=2 pn=3
   - Expected: b[0] equals `0x71`
   - Expected: b[1] equals `0x4A`
   - Expected: b[2] equals `0x00`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not_pred pd=1 pg=2 pn=3")
val b = emit_not_pred(1, 2, 3)
expect(b[0]).to_equal(0x71)
expect(b[1]).to_equal(0x4A)
expect(b[2]).to_equal(0x00)
expect(b[3]).to_equal(0x25)
```

</details>

### BRKA

#### brka pd=0 pg=1 pn=2

- brka pd=0 pg=1 pn=2
   - Expected: b[0] equals `0x40`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0x10`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("brka pd=0 pg=1 pn=2")
val b = emit_brka(0, 1, 2)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0x10)
expect(b[3]).to_equal(0x25)
```

</details>

#### brka pd=3 pg=7 pn=5

- brka pd=3 pg=7 pn=5
   - Expected: b[0] equals `0xA3`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0x10`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("brka pd=3 pg=7 pn=5")
val b = emit_brka(3, 7, 5)
expect(b[0]).to_equal(0xA3)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0x10)
expect(b[3]).to_equal(0x25)
```

</details>

### PNEXT

#### pnext_s pd=0 pg=1

- pnext_s pd=0 pg=1
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xC4`
   - Expected: b[2] equals `0x19`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pnext_s pd=0 pg=1")
val b = emit_pnext_s(0, 1)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xC4)
expect(b[2]).to_equal(0x19)
expect(b[3]).to_equal(0x25)
```

</details>

#### pnext_s pd=5 pg=3

- pnext_s pd=5 pg=3
   - Expected: b[0] equals `0x65`
   - Expected: b[1] equals `0xC4`
   - Expected: b[2] equals `0x19`
   - Expected: b[3] equals `0x25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pnext_s pd=5 pg=3")
val b = emit_pnext_s(5, 3)
expect(b[0]).to_equal(0x65)
expect(b[1]).to_equal(0xC4)
expect(b[2]).to_equal(0x19)
expect(b[3]).to_equal(0x25)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/sve2_pred_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SVE2 predicate emit golden bytes, PTRUE, PFALSE, WHILELT, WHILELE, AND predicate, ORR predicate, EOR predicate, NOT predicate, BRKA, PNEXT.
- SVE2 predicate emit golden bytes
- PTRUE
- PFALSE
- WHILELT
- WHILELE
- AND predicate
- ORR predicate
- EOR predicate
- NOT predicate
- BRKA
- PNEXT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `96f6c99c0500740c73ea01b59abe25cd423830035678fcab5bfac6473362acae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96f6c99c0500740c73ea01b59abe25cd423830035678fcab5bfac6473362acae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96f6c99c0500740c73ea01b59abe25cd423830035678fcab5bfac6473362acae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/sve2_pred_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/sve2_pred_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/sve2_pred_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/sve2_pred_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/sve2_pred_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/sve2_pred_emit_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ptrue_s pd=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/sve2_pred_emit_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ptrue_s pd=3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/sve2_pred_emit_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pfalse pd=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
