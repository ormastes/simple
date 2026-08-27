# U64 Shift Param Specification

> Tests covering u64 right shift via fn param, u64 right shift via overloaded fn (bind_args_with_values path).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 Shift Param Specification

## Scenarios

### u64 right shift via fn param

#### logical shift high-bit value (unsuffixed hex)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- logical shift high-bit value (unsuffixed hex)
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logical shift high-bit value (unsuffixed hex)")
# 0x8000000000000000 without u64 suffix parses as Value::Int(i64::MIN)
# coerce_unsigned must convert to UInt before shift
var result: u64 = shr_u64(0x8000000000000000)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

#### logical shift all-ones (unsuffixed hex)

- logical shift all-ones (unsuffixed hex)
   - Expected: result equals `0x7FFFFFFFFFFFFFFFu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logical shift all-ones (unsuffixed hex)")
# 0xFFFFFFFFFFFFFFFF without u64 suffix parses as Value::Int(-1)
var result: u64 = shr_u64(0xFFFFFFFFFFFFFFFF)
expect(result).to_equal(0x7FFFFFFFFFFFFFFFu64)
```

</details>

#### logical shift SHA-384 initial hash value (unsuffixed)

- logical shift SHA-384 initial hash value (unsuffixed)
   - Expected: result equals `0x0000000CBBB9D5DCu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logical shift SHA-384 initial hash value (unsuffixed)")
# 0xCBBB9D5DC1059ED8 parses as negative Value::Int
# This is the exact repro from the bug doc
var result: u64 = shr_u64_by(0xCBBB9D5DC1059ED8, 28)
expect(result).to_equal(0x0000000CBBB9D5DCu64)
```

</details>

#### no sign extension on high-bit u64 param (unsuffixed)

- no sign extension on high-bit u64 param (unsuffixed)
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no sign extension on high-bit u64 param (unsuffixed)")
var x: u64 = 0x8000000000000000
var result: u64 = shr_u64_by(x, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

### u64 right shift via overloaded fn (bind_args_with_values path)

#### overloaded: logical shift SHA-384 initial hash value

- overloaded: logical shift SHA-384 initial hash value
   - Expected: result equals `0x0000000CBBB9D5DCu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overloaded: logical shift SHA-384 initial hash value")
# This exercises Priority 4 overload dispatch -> exec_function_with_values
# -> bind_args_with_values which was missing coerce_unsigned
# The overload resolver pre-evaluates args then calls bind_args_with_values
var result: u64 = shift_right(0xCBBB9D5DC1059ED8, 28)
expect(result).to_equal(0x0000000CBBB9D5DCu64)
```

</details>

#### overloaded: logical shift high-bit value

- overloaded: logical shift high-bit value
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overloaded: logical shift high-bit value")
var result: u64 = shift_right(0x8000000000000000, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

#### overloaded: logical shift all-ones

- overloaded: logical shift all-ones
   - Expected: result equals `0x7FFFFFFFFFFFFFFFu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overloaded: logical shift all-ones")
var result: u64 = shift_right(0xFFFFFFFFFFFFFFFF, 1)
expect(result).to_equal(0x7FFFFFFFFFFFFFFFu64)
```

</details>

#### overloaded: no sign extension on high-bit variable

- overloaded: no sign extension on high-bit variable
   - Expected: result equals `0x4000000000000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overloaded: no sign extension on high-bit variable")
var x: u64 = 0x8000000000000000
var result: u64 = shift_right(x, 1)
expect(result).to_equal(0x4000000000000000u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u64_shift_param_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering u64 right shift via fn param, u64 right shift via overloaded fn (bind_args_with_values path).
- u64 right shift via fn param
- u64 right shift via overloaded fn (bind_args_with_values path)

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

- Canonical SPipe generation for source `8a40341262cf7b81a640f18bf6db371a0886b7fbbf7cf76d91f207df0e203fc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a40341262cf7b81a640f18bf6db371a0886b7fbbf7cf76d91f207df0e203fc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a40341262cf7b81a640f18bf6db371a0886b7fbbf7cf76d91f207df0e203fc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/u64_shift_param_spec.spl
mirror: doc/06_spec/01_unit/compiler/u64_shift_param_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/u64_shift_param_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/u64_shift_param_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/u64_shift_param_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logical shift high-bit value (unsuffixed hex)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u64_shift_param_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logical shift all-ones (unsuffixed hex)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u64_shift_param_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logical shift SHA-384 initial hash value (unsuffixed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
