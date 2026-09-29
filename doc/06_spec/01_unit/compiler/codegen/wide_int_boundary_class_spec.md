# Wide Int Boundary Class Specification

> Tests covering i64 values wider than the inline 61-bit tagged payload.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wide Int Boundary Class Specification

## Scenarios

### i64 values wider than the inline 61-bit tagged payload

#### keeps every boundary constant exact on the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every boundary constant exact on the interpreter
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- The interpreter is the control arm -- it was already correct, so a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps every boundary constant exact on the interpreter")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("The interpreter is the control arm -- it was already correct, so a red here means the probe is broken rather than the engine")
expect(interp).to_contain("PASS wide_i64_max")
expect(interp).to_contain("WIDE_INT_BOUNDARY PROBE: ALL PASS")
```

</details>

#### keeps the three filed constants exact on the cranelift JIT

- keeps the three filed constants exact on the cranelift JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the bug lived in
- 2^60 read back sign-flipped, 2^62 read back as 0, i64::MAX read back as -1
- Values just BELOW the limit must stay bit-identical -- the fix must not disturb the inline fast path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the three filed constants exact on the cranelift JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit -- the engine the bug lived in")
val jit = run_probe_in_mode("jit")

step("2^60 read back sign-flipped, 2^62 read back as 0, i64::MAX read back as -1")
expect(jit).to_contain("PASS wide_p60")
expect(jit).to_contain("PASS wide_p62")
expect(jit).to_contain("PASS wide_i64_max")

step("Values just BELOW the limit must stay bit-identical -- the fix must not disturb the inline fast path")
expect(jit).to_contain("PASS inline_p59")
expect(jit).to_contain("PASS inline_neg_p59")
```

</details>

#### keeps the whole wide-int class exact on the cranelift JIT

- keeps the whole wide-int class exact on the cranelift JIT
- Wide NEGATIVE values must not surface as huge positives -- the failure mode of boxing them as unsigned
- Every erased-slot boundary: array element, return value, nullable
- Arithmetic forces a real decode -- a value corrupted identically in and out could still print correctly
- Equality and ordering across the inline/wide split: two wide values are separate heap boxes, so a raw-bits compare would call equal values unequal
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the whole wide-int class exact on the cranelift JIT")
val jit = run_probe_in_mode("jit")

step("Wide NEGATIVE values must not surface as huge positives -- the failure mode of boxing them as unsigned")
expect(jit).to_contain("PASS wide_neg_p60")
expect(jit).to_contain("PASS wide_neg_p62")
expect(jit).to_contain("PASS wide_i64_min")

step("Every erased-slot boundary: array element, return value, nullable")
expect(jit).to_contain("PASS array_wide_p60")
expect(jit).to_contain("PASS array_wide_max")
expect(jit).to_contain("PASS array_wide_neg")
expect(jit).to_contain("PASS return_wide_max")
expect(jit).to_contain("PASS optional_wide_p62")

step("Arithmetic forces a real decode -- a value corrupted identically in and out could still print correctly")
expect(jit).to_contain("PASS wide_arith_sub")
expect(jit).to_contain("PASS wide_arith_div")
expect(jit).to_contain("PASS wide_arith_shift")

step("Equality and ordering across the inline/wide split: two wide values are separate heap boxes, so a raw-bits compare would call equal values unequal")
expect(jit).to_contain("PASS wide_eq_same")
expect(jit).to_contain("PASS wide_ne_diff")
expect(jit).to_contain("PASS wide_gt_inline")
expect(jit).to_contain("PASS wide_neg_lt_zero")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("WIDE_INT_BOUNDARY PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i64 values wider than the inline 61-bit tagged payload.
- i64 values wider than the inline 61-bit tagged payload

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

- Canonical SPipe generation for source `4315df37bca3925f7616eda9c68af476fd81b1dfd5eb5f7fa8f0c5c308440f9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4315df37bca3925f7616eda9c68af476fd81b1dfd5eb5f7fa8f0c5c308440f9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4315df37bca3925f7616eda9c68af476fd81b1dfd5eb5f7fa8f0c5c308440f9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/wide_int_boundary_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/wide_int_boundary_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/wide_int_boundary_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every boundary constant exact on the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the three filed constants exact on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/wide_int_boundary_class_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the whole wide-int class exact on the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
