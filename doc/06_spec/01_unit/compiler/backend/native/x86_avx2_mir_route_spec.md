# X86 Avx2 Mir Route Specification

> Tests covering x86 AVX2 typed MIR route.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Avx2 Mir Route Specification

## Scenarios

### x86 AVX2 typed MIR route

#### reuses YMM registers for more than eight sequential destinations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses YMM registers for more than eight sequential destinations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses YMM registers for more than eight sequential destinations")
val module = isel_module_with_avx2_capability(avx2_reuse_module(), avx2_capability())
val block = module.functions[0].blocks[1]
var used: Dict<i64, bool> = {}
var vector_ops = 0
for inst in block.insts:
    if inst.opcode == X86_OP_VADDPS_YMM:
        vector_ops = vector_ops + 1
        for operand in inst.operands:
            match operand.kind:
                case Reg(reg): used[reg_id(reg)] = true
                case _: ()
assert_equal(vector_ops, 10)
assert_true(used.keys().len() <= 3)
```

</details>

#### keeps nine simultaneously live vectors fail closed

- keeps nine simultaneously live vectors fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps nine simultaneously live vectors fail closed")
val plan = x86_plan_avx2_f32x8(avx2_pressure_function())
assert_equal(plan.ok, false)
assert_equal(plan.reason, "simd-register-pressure")
```

</details>

#### rejects multi-block SIMD until CFG liveness is authoritative

- rejects multi-block SIMD until CFG liveness is authoritative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects multi-block SIMD until CFG liveness is authoritative")
val plan = x86_plan_avx2_f32x8(avx2_multiblock_function())
assert_equal(plan.ok, false)
assert_equal(plan.reason, "simd-cfg-liveness-unavailable")
```

</details>

#### selects aligned f32x8 MIR without scalar NOP substitution

- selects aligned f32x8 MIR without scalar NOP substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects aligned f32x8 MIR without scalar NOP substitution")
val module = selected_module()
val block = module.functions[0].blocks[1]
assert_equal(block.insts.len(), 4)
assert_equal(block.insts[0].opcode, X86_OP_VMOVAPS_LOAD_YMM)
assert_equal(block.insts[1].opcode, X86_OP_VMOVAPS_LOAD_YMM)
assert_equal(block.insts[2].opcode, X86_OP_VADDPS_YMM)
assert_equal(block.insts[3].opcode, X86_OP_VMOVAPS_STORE_YMM)
```

</details>

#### preserves YMM classes through scalar pointer allocation

- preserves YMM classes through scalar pointer allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves YMM classes through scalar pointer allocation")
val module = regalloc_module(selected_module())
val block = module.functions[0].blocks[1]
for inst in block.insts:
    if inst.opcode == X86_OP_VADDPS_YMM:
        for operand in inst.operands:
            match operand.kind:
                case Reg(reg):
                    val id = reg_id(reg)
                    assert_true(id >= X86_YMM0 and id <= X86_YMM7)
                case _: assert_true(false)
```

</details>

#### encodes the selected load add store route as AVX2 bytes

- encodes the selected load add store route as AVX2 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the selected load add store route as AVX2 bytes")
val allocated = regalloc_module(selected_module())
val encoded = encode_module(allocated)[0].code
assert_true(contains_bytes(encoded, [0xC4, 0xE1, 0x7C, 0x28, 0x83, 0, 0, 0, 0]))
assert_true(contains_bytes(encoded, [0xC4, 0xC1, 0x7C, 0x28, 0x8C, 0x24, 0, 0, 0, 0]))
assert_true(contains_bytes(encoded, [0xC4, 0xE1, 0x7C, 0x58, 0xD1]))
assert_true(contains_bytes(encoded, [0xC4, 0xC1, 0x7C, 0x29, 0x95, 0, 0, 0, 0]))
```

</details>

#### carries a deterministic target capability receipt

- carries a deterministic target capability receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries a deterministic target capability receipt")
assert_equal(native_avx2_receipt_key(avx2_capability()),
    "native-avx2/v1|target=x86_64-unknown-linux-gnu|source=unit-injected|hash=fixture-avx2-v1|admitted=true|reason=avx2-capability-admitted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86 AVX2 typed MIR route.
- x86 AVX2 typed MIR route

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `24f77e16beb7b4bb2bcf3674a43274ff345b91949adac75724c9e85ee2e5502f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24f77e16beb7b4bb2bcf3674a43274ff345b91949adac75724c9e85ee2e5502f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24f77e16beb7b4bb2bcf3674a43274ff345b91949adac75724c9e85ee2e5502f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses YMM registers for more than eight sequential destinations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps nine simultaneously live vectors fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/native/x86_avx2_mir_route_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects multi-block SIMD until CFG liveness is authoritative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
