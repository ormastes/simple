# mir_instruction_complete_spec

> Purpose: Prove that Mir Instruction Complete.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mir_instruction_complete_spec

Purpose: Prove that Mir Instruction Complete.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/mir_instruction_complete_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Mir Instruction Complete.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Mir Instruction Complete

#### emits core builder instructions in order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits core builder instructions in order
- Verify: emits core builder instructions in order
   - Expected: tc.instructions.len() equals `5`
   - Expected: tc.instructions[0] equals `MirTestInst.ConstInt(VReg(id: 0), 10)`
   - Expected: tc.instructions[1] equals `MirTestInst.ConstBool(VReg(id: 1), true)`
   - Expected: tc.instructions[2] equals `MirTestInst.Add(VReg(id: 2), VReg(id: 0), VReg(id: 0))`
   - Expected: tc.instructions[4] equals `MirTestInst.Ret(VReg(id: 2))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits core builder instructions in order")
step("Verify: emits core builder instructions in order")
# @req: REQ-COMP-MIR-INSTRUCTION-COMPLETE-001
val builder = new_builder("core")
builder.add_const_int(0, 10)
builder.add_const_bool(1, true)
builder.add_add(2, 0, 0)
builder.add_branch(1, 3, 4)
builder.add_ret(2)

val tc = builder.build()

expect(tc.instructions.len()).to_equal(5)
expect(tc.instructions[0]).to_equal(MirTestInst.ConstInt(VReg(id: 0), 10))
expect(tc.instructions[1]).to_equal(MirTestInst.ConstBool(VReg(id: 1), true))
expect(tc.instructions[2]).to_equal(MirTestInst.Add(VReg(id: 2), VReg(id: 0), VReg(id: 0)))
expect(tc.instructions[4]).to_equal(MirTestInst.Ret(VReg(id: 2)))
```

</details>

#### tracks the next virtual register from sparse destinations

- tracks the next virtual register from sparse destinations
- Verify: tracks the next virtual register from sparse destinations
   - Expected: builder.next_vreg equals `0`
   - Expected: builder.next_vreg equals `6`
   - Expected: builder.next_vreg equals `6`
   - Expected: builder.next_vreg equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks the next virtual register from sparse destinations")
step("Verify: tracks the next virtual register from sparse destinations")
val builder = new_builder("vregs")

expect(builder.next_vreg).to_equal(0)
builder.add_const_int(5, 100)
expect(builder.next_vreg).to_equal(6)
builder.add_gpu_global_id(2, 0)
expect(builder.next_vreg).to_equal(6)
builder.add_mul(20, 5, 2)
expect(builder.next_vreg).to_equal(21)
```

</details>

#### supports explicit backend restrictions

- supports explicit backend restrictions
- Verify: supports explicit backend restrictions
   - Expected: tc.expected_backends.len() equals `2`
   - Expected: tc.expected_backends[0] equals `BackendTarget.LLVM`
   - Expected: tc.expected_backends[1] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports explicit backend restrictions")
step("Verify: supports explicit backend restrictions")
val builder = new_builder("backends")
builder.only_backends([BackendTarget.LLVM, BackendTarget.Interpreter])

val tc = builder.build()

expect(tc.expected_backends.len()).to_equal(2)
expect(tc.expected_backends[0]).to_equal(BackendTarget.LLVM)
expect(tc.expected_backends[1]).to_equal(BackendTarget.Interpreter)
```

</details>

#### keeps helper patterns deterministic

- keeps helper patterns deterministic
- Verify: keeps helper patterns deterministic
   - Expected: arithmetic.name equals `simple_arithmetic`
   - Expected: arithmetic.instructions.len() equals `4`
   - Expected: simd.expected_backends equals `[BackendTarget.LLVM, BackendTarget.Interpreter]`
   - Expected: gpu_case.expected_backends equals `[BackendTarget.Vulkan]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps helper patterns deterministic")
step("Verify: keeps helper patterns deterministic")
val arithmetic = simple_arithmetic()
val simd = simd_reduction()
val gpu_case = gpu_kernel()

expect(arithmetic.name).to_equal("simple_arithmetic")
expect(arithmetic.instructions.len()).to_equal(4)
expect(simd.expected_backends).to_equal([BackendTarget.LLVM, BackendTarget.Interpreter])
expect(gpu_case.expected_backends).to_equal([BackendTarget.Vulkan])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-MIR-INSTRUCTION-COMPLETE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b61dd5d1cdb2e7e95b05ee3e798985fea3754e22668a49d5c320b80e2d750c09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b61dd5d1cdb2e7e95b05ee3e798985fea3754e22668a49d5c320b80e2d750c09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b61dd5d1cdb2e7e95b05ee3e798985fea3754e22668a49d5c320b80e2d750c09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/mir_instruction_complete_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/mir_instruction_complete_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/mir_instruction_complete_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/mir_instruction_complete_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/mir_instruction_complete_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/mir_instruction_complete_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits core builder instructions in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/mir_instruction_complete_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks the next virtual register from sparse destinations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/mir_instruction_complete_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports explicit backend restrictions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
