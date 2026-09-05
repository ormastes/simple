# Strength Reduction Specification

> Tests covering MIR strength reduction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Strength Reduction Specification

## Scenarios

### MIR strength reduction

#### declares a reusable built-in MIR pipeline optimization provider

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares a reusable built-in MIR pipeline optimization provider
   - Expected: provider.name equals `simple.opt.math.strength_reduce`
   - Expected: provider.kind equals `OptimizerProviderKind.Mir`
   - Expected: provider.lookup_kind equals `OptimizerRuleLookupKind.PipelinePass`
   - Expected: optimization_rule_provider_is_pipeline_pass(provider) is true
   - Expected: optimization_rule_provider_has_required_fact(provider, "integer_widths") is true
   - Expected: optimization_rule_provider_has_required_fact(provider, "non_negative_or_unsigned_operands") is true
   - Expected: provider.produced_facts[0] equals `canonical_integer_arithmetic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares a reusable built-in MIR pipeline optimization provider")
val provider = strength_reduction_provider()
expect(provider.name).to_equal("simple.opt.math.strength_reduce")
expect(provider.kind).to_equal(OptimizerProviderKind.Mir)
expect(provider.lookup_kind).to_equal(OptimizerRuleLookupKind.PipelinePass)
expect(optimization_rule_provider_is_pipeline_pass(provider)).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "integer_widths")).to_equal(true)
expect(optimization_rule_provider_has_required_fact(provider, "non_negative_or_unsigned_operands")).to_equal(true)
expect(provider.produced_facts[0]).to_equal("canonical_integer_arithmetic")
```

</details>

#### lowers net-driver style modulo by 128 to bitmask

- lowers net-driver style modulo by 128 to bitmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers net-driver style modulo by 128 to bitmask")
_sr_expect_bitand_mask(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Rem, _sr_copy(1), _sr_int(128)), span: nil)),
    127
)
```

</details>

#### lowers 64-bit power-of-two modulo constants to bitmask

- lowers 64-bit power-of-two modulo constants to bitmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers 64-bit power-of-two modulo constants to bitmask")
_sr_expect_bitand_mask(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Rem, _sr_copy(1), _sr_int(1099511627776)), span: nil)),
    1099511627775
)
```

</details>

#### removes bit-or zero identity

- removes bit-or zero identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes bit-or zero identity")
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitOr, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### removes bit-xor zero identity

- removes bit-xor zero identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes bit-xor zero identity")
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitXor, _sr_int(0), _sr_copy(1)), span: nil)),
    1
)
```

</details>

#### folds bit-and zero annihilator

- folds bit-and zero annihilator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("folds bit-and zero annihilator")
_sr_expect_int_const(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.BitAnd, _sr_copy(1), _sr_int(0)), span: nil)),
    0
)
```

</details>

#### removes zero left shift

- removes zero left shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes zero left shift")
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Shl, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### removes zero right shift

- removes zero right shift


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes zero right shift")
_sr_expect_copy_from(
    _sr_reduce_one(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Shr, _sr_copy(1), _sr_int(0)), span: nil)),
    1
)
```

</details>

#### decomposes multiply by 6 into two shifts and add

- decomposes multiply by 6 into two shifts and add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 6 into two shifts and add")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(6)), span: nil))
expect kinds.len() == 3
_sr_expect_shift_amount(kinds[0], 2)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
```

</details>

#### decomposes multiply by 14 into two shifts and subtract

- decomposes multiply by 14 into two shifts and subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 14 into two shifts and subtract")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(14), _sr_copy(1)), span: nil))
expect kinds.len() == 3
_sr_expect_shift_amount(kinds[0], 4)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Sub)
```

</details>

#### decomposes multiply by 11 into two shifts plus source add

- decomposes multiply by 11 into two shifts plus source add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 11 into two shifts plus source add")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(11)), span: nil))
expect kinds.len() == 4
_sr_expect_shift_amount(kinds[0], 3)
_sr_expect_shift_amount(kinds[1], 1)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
_sr_expect_binop_kind(kinds[3], MirBinOp.Add)
```

</details>

#### decomposes multiply by 13 into two shifts plus source add

- decomposes multiply by 13 into two shifts plus source add


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 13 into two shifts plus source add")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(13), _sr_copy(1)), span: nil))
expect kinds.len() == 4
_sr_expect_shift_amount(kinds[0], 3)
_sr_expect_shift_amount(kinds[1], 2)
_sr_expect_binop_kind(kinds[2], MirBinOp.Add)
_sr_expect_binop_kind(kinds[3], MirBinOp.Add)
```

</details>

#### decomposes multiply by 17 into shift and add

- decomposes multiply by 17 into shift and add


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 17 into shift and add")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_copy(1), _sr_int(17)), span: nil))
expect kinds.len() == 2
_sr_expect_shift_amount(kinds[0], 4)
_sr_expect_binop_kind(kinds[1], MirBinOp.Add)
```

</details>

#### decomposes multiply by 31 into shift and subtract

- decomposes multiply by 31 into shift and subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decomposes multiply by 31 into shift and subtract")
val kinds = _sr_reduce_all(MirInst(kind: MirInstKind.BinOp(_sr_lid(2), MirBinOp.Mul, _sr_int(31), _sr_copy(1)), span: nil))
expect kinds.len() == 2
_sr_expect_shift_amount(kinds[0], 5)
_sr_expect_binop_kind(kinds[1], MirBinOp.Sub)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/strength_reduction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR strength reduction.
- MIR strength reduction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `5a1fc34bf6140c9ee248393dc60527cdc17198794fe1a534d966219d0b3f9429`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a1fc34bf6140c9ee248393dc60527cdc17198794fe1a534d966219d0b3f9429`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a1fc34bf6140c9ee248393dc60527cdc17198794fe1a534d966219d0b3f9429`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir_opt/strength_reduction_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/strength_reduction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/strength_reduction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/strength_reduction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/strength_reduction_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares a reusable built-in MIR pipeline optimization provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/strength_reduction_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers net-driver style modulo by 128 to bitmask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/strength_reduction_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers 64-bit power-of-two modulo constants to bitmask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
