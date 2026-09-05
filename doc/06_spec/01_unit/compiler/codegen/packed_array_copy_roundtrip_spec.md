# Packed Array Copy Roundtrip Specification

> Tests covering copying a [u64] binding preserves small element values, copying a [u64] binding preserves large element values, length was never the failing signal, both execution engines agree on packed array copies.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Array Copy Roundtrip Specification

## Scenarios

### copying a [u64] binding preserves small element values

#### carries a small value through instead of dividing it by eight

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- carries a small value through instead of dividing it by eight
- Build a packed [u64] whose first element is 5
- Bind it to a second name, which lowers to rt_array_copy
- Read the copy back and compare against the absolute stored value
   - Expected: copied[0] equals `5u64`
   - Expected: copied[1] equals `6u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries a small value through instead of dividing it by eight")
step("Build a packed [u64] whose first element is 5")
val original = _small_u64()

step("Bind it to a second name, which lowers to rt_array_copy")
val copied = original

step("Read the copy back and compare against the absolute stored value")
expect(copied[0]).to_equal(5u64)
expect(copied[1]).to_equal(6u64)
```

</details>

#### leaves the source array untouched

- leaves the source array untouched
- Confirm copying did not disturb the original
   - Expected: original[0] equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves the source array untouched")
step("Confirm copying did not disturb the original")
val original = _small_u64()
val copied = original
expect(original[0]).to_equal(5u64)
```

</details>

### copying a [u64] binding preserves large element values

#### carries a value that a divide-by-eight would visibly corrupt

- carries a value that a divide-by-eight would visibly corrupt
- Build a packed [u64] holding a large word and the u64 maximum
- Bind it to a second name and read both elements back
   - Expected: copied[0] equals `1234567890123456789u64`
   - Expected: copied[1] equals `18446744073709551615u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("carries a value that a divide-by-eight would visibly corrupt")
# 1234567890123456789 / 8 == 154320986265432098. Asserting the exact
# original is what distinguishes a real copy from a shifted one.
step("Build a packed [u64] holding a large word and the u64 maximum")
val original = _large_u64()

step("Bind it to a second name and read both elements back")
val copied = original
expect(copied[0]).to_equal(1234567890123456789u64)
expect(copied[1]).to_equal(18446744073709551615u64)
```

</details>

### length was never the failing signal

#### reports the length that the elements should back

- reports the length that the elements should back
- Confirm the copy reports two elements
   - Expected: copied.length() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the length that the elements should back")
# The length was correct throughout the defect, so this assertion is
# the one that would MISS it. Kept as context for the element checks
# above, never as a substitute for them.
step("Confirm the copy reports two elements")
val original = _small_u64()
val copied = original
expect(copied.length()).to_equal(2)
```

</details>

### both execution engines agree on packed array copies

#### produces identical correct output under the JIT and the interpreter

- produces identical correct output under the JIT and the interpreter
- Run the same repro program under the cranelift JIT
- Run it again under the tree-walk interpreter
- The JIT must report the stored values, not the values shifted right by three
- The divide-by-eight signatures must be absent from the JIT output
   - Expected: jit_out does not contain `154320986265432098`
- The interpreter was always correct and must stay that way
- Both engines must agree byte for byte
   - Expected: jit_out equals `interp_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces identical correct output under the JIT and the interpreter")
step("Run the same repro program under the cranelift JIT")
val jit_out = _run_repro_in_mode("jit")

step("Run it again under the tree-walk interpreter")
val interp_out = _run_repro_in_mode("interpreter")

step("The JIT must report the stored values, not the values shifted right by three")
expect(jit_out).to_contain("5")
expect(jit_out).to_contain("1234567890123456789")
expect(jit_out).to_contain("18446744073709551615")

step("The divide-by-eight signatures must be absent from the JIT output")
expect(jit_out.contains("154320986265432098")).to_equal(false)

step("The interpreter was always correct and must stay that way")
expect(interp_out).to_contain("1234567890123456789")

step("Both engines must agree byte for byte")
expect(jit_out).to_equal(interp_out)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering copying a [u64] binding preserves small element values, copying a [u64] binding preserves large element values, length was never the failing signal, both execution engines agree on packed array copies.
- copying a [u64] binding preserves small element values
- copying a [u64] binding preserves large element values
- length was never the failing signal
- both execution engines agree on packed array copies

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `3b561f1c0b8e573e2c3ab35ef11cb79a7fae1ef7fa7a3b9dcc9e06f916d0cee1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b561f1c0b8e573e2c3ab35ef11cb79a7fae1ef7fa7a3b9dcc9e06f916d0cee1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b561f1c0b8e573e2c3ab35ef11cb79a7fae1ef7fa7a3b9dcc9e06f916d0cee1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries a small value through instead of dividing it by eight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves the source array untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries a value that a divide-by-eight would visibly corrupt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
