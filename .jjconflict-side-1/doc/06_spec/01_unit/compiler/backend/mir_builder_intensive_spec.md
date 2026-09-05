# mir_builder_intensive_spec

> Purpose: Prove that Mir Builder Intensive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mir_builder_intensive_spec

Purpose: Prove that Mir Builder Intensive.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/mir_builder_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Mir Builder Intensive.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Mir Builder Intensive

#### emits mixed builder instructions in order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits mixed builder instructions in order
- Verify: emits mixed builder instructions in order
   - Expected: tc.instructions.len() equals `7`
   - Expected: tc.instructions[0] equals `MirTestInst.ConstInt(VReg(id: 0), 0)`
   - Expected: tc.instructions[1] equals `MirTestInst.ConstFloat(VReg(id: 1), 3.5)`
   - Expected: tc.instructions[2] equals `MirTestInst.ConstBool(VReg(id: 2), true)`
   - Expected: tc.instructions[3] equals `MirTestInst.Add(VReg(id: 3), VReg(id: 0), VReg(id: 0))`
   - Expected: tc.instructions[4] equals `MirTestInst.Mul(VReg(id: 4), VReg(id: 3), VReg(id: 0))`
   - Expected: tc.instructions[5] equals `MirTestInst.Branch(VReg(id: 2), BlockId(id: 10), BlockId(id: 20))`
   - Expected: tc.instructions[6] equals `MirTestInst.Ret(VReg(id: 4))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits mixed builder instructions in order")
step("Verify: emits mixed builder instructions in order")
# @req: REQ-COMP-MIR-BUILDER-INTENSIVE-001
val builder = new_builder("intensive")
builder.add_const_int(0, 0)
builder.add_const_float(1, 3.5)
builder.add_const_bool(2, true)
builder.add_add(3, 0, 0)
builder.add_mul(4, 3, 0)
builder.add_branch(2, 10, 20)
builder.add_ret(4)

val tc = builder.build()

expect(tc.instructions.len()).to_equal(7)
expect(tc.instructions[0]).to_equal(MirTestInst.ConstInt(VReg(id: 0), 0))
expect(tc.instructions[1]).to_equal(MirTestInst.ConstFloat(VReg(id: 1), 3.5))
expect(tc.instructions[2]).to_equal(MirTestInst.ConstBool(VReg(id: 2), true))
expect(tc.instructions[3]).to_equal(MirTestInst.Add(VReg(id: 3), VReg(id: 0), VReg(id: 0)))
expect(tc.instructions[4]).to_equal(MirTestInst.Mul(VReg(id: 4), VReg(id: 3), VReg(id: 0)))
expect(tc.instructions[5]).to_equal(MirTestInst.Branch(VReg(id: 2), BlockId(id: 10), BlockId(id: 20)))
expect(tc.instructions[6]).to_equal(MirTestInst.Ret(VReg(id: 4)))
```

</details>

#### tracks sparse virtual register usage

- tracks sparse virtual register usage
- Verify: tracks sparse virtual register usage
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
step("tracks sparse virtual register usage")
step("Verify: tracks sparse virtual register usage")
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

#### preserves backend selection overrides

- preserves backend selection overrides
- Verify: preserves backend selection overrides
   - Expected: tc.expected_backends.len() equals `1`
   - Expected: tc.expected_backends[0] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves backend selection overrides")
step("Verify: preserves backend selection overrides")
val builder = new_builder("backends")
builder.only_backend(BackendTarget.Interpreter)

val tc = builder.build()

expect(tc.expected_backends.len()).to_equal(1)
expect(tc.expected_backends[0]).to_equal(BackendTarget.Interpreter)
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
- `REQ-COMP-MIR-BUILDER-INTENSIVE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f5fe4c9b40988a7c21d95a7634bc44df2f2b11af2dcc7f1cc9213165aca3c75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f5fe4c9b40988a7c21d95a7634bc44df2f2b11af2dcc7f1cc9213165aca3c75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f5fe4c9b40988a7c21d95a7634bc44df2f2b11af2dcc7f1cc9213165aca3c75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/mir_builder_intensive_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/mir_builder_intensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/mir_builder_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/mir_builder_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/mir_builder_intensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/mir_builder_intensive_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits mixed builder instructions in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/mir_builder_intensive_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks sparse virtual register usage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/mir_builder_intensive_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves backend selection overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
