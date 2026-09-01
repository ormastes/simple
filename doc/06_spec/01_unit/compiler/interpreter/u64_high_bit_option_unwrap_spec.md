# High-bit u64 Option-of-struct round trip

> Regression for `interp_u64_high_bit_option_unwrap_corruption`. A `u64` field

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# High-bit u64 Option-of-struct round trip

Regression for `interp_u64_high_bit_option_unwrap_corruption`. A `u64` field

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression for `interp_u64_high_bit_option_unwrap_corruption`. A `u64` field
must keep unsigned ordering when the enclosing struct is selected in a loop,
returned as `Frame?`, and consumed by `if val`.

## Scenarios

### high-bit u64 optional struct unwrap

#### preserves the exact 2^63 boundary through selection return and unwrap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves the exact 2^63 boundary through selection return and unwrap
- Select a struct whose u64 field has the first high-bit value
- Return it as Frame? and unwrap it with if val
   - Expected: selected_checksum(edge).to_text() equals `9223372036854775808`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves the exact 2^63 boundary through selection return and unwrap")
step("Select a struct whose u64 field has the first high-bit value")
val edge = 9223372036854775808u64

step("Return it as Frame? and unwrap it with if val")
expect(selected_checksum(edge).to_text()).to_equal("9223372036854775808")
```

</details>

#### preserves adjacent and maximum u64 values through the same boundary

- preserves adjacent and maximum u64 values through the same boundary
- Exercise the value immediately below the high bit
   - Expected: selected_checksum(9223372036854775807u64).to_text() equals `9223372036854775807`
- Exercise the value immediately above the high bit
   - Expected: selected_checksum(9223372036854775809u64).to_text() equals `9223372036854775809`
- Exercise the maximum u64 value
   - Expected: selected_checksum(18446744073709551615u64).to_text() equals `18446744073709551615`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves adjacent and maximum u64 values through the same boundary")
step("Exercise the value immediately below the high bit")
expect(selected_checksum(9223372036854775807u64).to_text()).to_equal("9223372036854775807")

step("Exercise the value immediately above the high bit")
expect(selected_checksum(9223372036854775809u64).to_text()).to_equal("9223372036854775809")

step("Exercise the maximum u64 value")
expect(selected_checksum(18446744073709551615u64).to_text()).to_equal("18446744073709551615")
```

</details>

#### keeps mixed signed and unsigned ordering semantic at the same boundary

- keeps mixed signed and unsigned ordering semantic at the same boundary
- Compare the maximum u64 against the maximum i64
   - Expected: 18446744073709551615u64 > 9223372036854775807 is true
- Compare a negative i64 against a high-bit u64
   - Expected: -1 < 9223372036854775808u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps mixed signed and unsigned ordering semantic at the same boundary")
step("Compare the maximum u64 against the maximum i64")
expect(18446744073709551615u64 > 9223372036854775807).to_equal(true)

step("Compare a negative i64 against a high-bit u64")
expect(-1 < 9223372036854775808u64).to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `7ac8f87802b43fb0045f15202a840c5dbe92012212830f79560d540be47fc80f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7ac8f87802b43fb0045f15202a840c5dbe92012212830f79560d540be47fc80f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7ac8f87802b43fb0045f15202a840c5dbe92012212830f79560d540be47fc80f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the exact 2^63 boundary through selection return and unwrap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves adjacent and maximum u64 values through the same boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/u64_high_bit_option_unwrap_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps mixed signed and unsigned ordering semantic at the same boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
