# u128_lowering_spec

> Purpose: Prove that u128 and i128 annotations lower through HIR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# u128_lowering_spec

Purpose: Prove that u128 and i128 annotations lower through HIR.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u128_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that u128 and i128 annotations lower through HIR.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### u128 and i128 annotations lower through HIR

#### accepts a u128 parameter and returns an exact product

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a u128 parameter and returns an exact product
- Verify: accepts a u128 parameter and returns an exact product
   - Expected: u128_mul(LIMB_A, SCALAR_S) equals `1099511627776000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a u128 parameter and returns an exact product")
step("Verify: accepts a u128 parameter and returns an exact product")
# @req: REQ-COMP-U128-AND-I128-ANNOTATIONS-LOWER-THROUGH-001
expect(u128_mul(LIMB_A, SCALAR_S)).to_equal(1099511627776000)
```

</details>

#### accepts an i128 parameter and returns an exact sum

- accepts an i128 parameter and returns an exact sum
- Verify: accepts an i128 parameter and returns an exact sum
   - Expected: i128_add(576460752303423000, 488) equals `576460752303423488`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts an i128 parameter and returns an exact sum")
step("Verify: accepts an i128 parameter and returns an exact sum")
expect(i128_add(576460752303423000, 488)).to_equal(576460752303423488)
```

</details>

#### shifts a u128 value right arithmetically like the interpreter

- shifts a u128 value right arithmetically like the interpreter
- Verify: shifts a u128 value right arithmetically like the interpreter
   - Expected: u128_shr(1099511627776000, 51) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shifts a u128 value right arithmetically like the interpreter")
step("Verify: shifts a u128 value right arithmetically like the interpreter")
expect(u128_shr(1099511627776000, 51)).to_equal(0)
```

</details>

#### shifts a wider u128 value right across the 51-bit boundary

- shifts a wider u128 value right across the 51-bit boundary
- Verify: shifts a wider u128 value right across the 51-bit boundary
   - Expected: u128_shr(36028797018963968, 51) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shifts a wider u128 value right across the 51-bit boundary")
step("Verify: shifts a wider u128 value right across the 51-bit boundary")
# 2^55 >> 51 == 2^4 == 16
expect(u128_shr(36028797018963968, 51)).to_equal(16)
```

</details>

#### masks a u128 value to 51 bits

- masks a u128 value to 51 bits
- Verify: masks a u128 value to 51 bits
   - Expected: u128_and(36028797018963968, LIMB_MASK) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("masks a u128 value to 51 bits")
step("Verify: masks a u128 value to 51 bits")
expect(u128_and(36028797018963968, LIMB_MASK)).to_equal(0)
```

</details>

### u128 carry chain matches curve25519 field arithmetic

#### splits the low 51 bits off a limb product

- splits the low 51 bits off a limb product
- Verify: splits the low 51 bits off a limb product
   - Expected: carry_low(36028797018963968, 1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("splits the low 51 bits off a limb product")
step("Verify: splits the low 51 bits off a limb product")
# 2^55 * 1 = 2^55; low 51 bits are zero, so the whole value carries.
expect(carry_low(36028797018963968, 1)).to_equal(0)
```

</details>

#### produces the matching carry-out

- produces the matching carry-out
- Verify: produces the matching carry-out
   - Expected: carry_out(36028797018963968, 1) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces the matching carry-out")
step("Verify: produces the matching carry-out")
expect(carry_out(36028797018963968, 1)).to_equal(16)
```

</details>

#### keeps a sub-2^51 product entirely in the low word with no carry

- keeps a sub-2^51 product entirely in the low word with no carry
- Verify: keeps a sub-2^51 product entirely in the low word with no carry
   - Expected: carry_low(LIMB_A, SCALAR_S) equals `1099511627776000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a sub-2^51 product entirely in the low word with no carry")
step("Verify: keeps a sub-2^51 product entirely in the low word with no carry")
expect(carry_low(LIMB_A, SCALAR_S)).to_equal(1099511627776000)
```

</details>

#### emits no carry when the product fits in 51 bits

- emits no carry when the product fits in 51 bits
- Verify: emits no carry when the product fits in 51 bits
   - Expected: carry_out(LIMB_A, SCALAR_S) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits no carry when the product fits in 51 bits")
step("Verify: emits no carry when the product fits in 51 bits")
expect(carry_out(LIMB_A, SCALAR_S)).to_equal(0)
```

</details>

#### propagates a carry into the next limb

- propagates a carry into the next limb
- Verify: propagates a carry into the next limb
   - Expected: two_limb_carry(36028797018963968, 1099511627776, 1) equals `1099511627792`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("propagates a carry into the next limb")
step("Verify: propagates a carry into the next limb")
# a0 * s = 2^55 -> carry 16; a1 * s = 2^40 * 1 = 2^40.
# n1 = 2^40 + 16 = 1099511627792
expect(two_limb_carry(36028797018963968, 1099511627776, 1)).to_equal(1099511627792)
```

</details>

#### adds no carry when the low limb does not overflow 51 bits

- adds no carry when the low limb does not overflow 51 bits
- Verify: adds no carry when the low limb does not overflow 51 bits
   - Expected: two_limb_carry(1, 1099511627776, 1) equals `1099511627776`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("adds no carry when the low limb does not overflow 51 bits")
step("Verify: adds no carry when the low limb does not overflow 51 bits")
expect(two_limb_carry(1, 1099511627776, 1)).to_equal(1099511627776)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-U128-AND-I128-ANNOTATIONS-LOWER-THROUGH-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6d40bf57a1138a2f18bc076ee144b29e491425cae8fb7fee33e0d9cef82f7f00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d40bf57a1138a2f18bc076ee144b29e491425cae8fb7fee33e0d9cef82f7f00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d40bf57a1138a2f18bc076ee144b29e491425cae8fb7fee33e0d9cef82f7f00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/u128_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/u128_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/u128_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/u128_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/u128_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/u128_lowering_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a u128 parameter and returns an exact product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u128_lowering_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an i128 parameter and returns an exact sum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u128_lowering_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shifts a u128 value right arithmetically like the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
