# Cranelift Gemm Fusion Specification

> Tests covering Cranelift GEMM-add fusion detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cranelift Gemm Fusion Specification

## Scenarios

### Cranelift GEMM-add fusion detection

#### detects adjacent MatMul consumed once by BroadcastAdd

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects adjacent MatMul consumed once by BroadcastAdd
   - Expected: plan.is_some() is true
   - Expected: plan.unwrap().dest.id equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects adjacent MatMul consumed once by BroadcastAdd")
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val add = binop_inst(4, MirBinOp.BroadcastAdd, 3, 2)
val func = test_func([matmul, add], MirTerminator.Ret(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, add)
expect(plan.is_some()).to_equal(true)
if plan.is_some():
    expect(plan.unwrap().dest.id).to_equal(4)
```

</details>

#### does not fuse when the MatMul temp has a second use

- does not fuse when the MatMul temp has a second use
   - Expected: plan.is_some() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fuse when the MatMul temp has a second use")
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val add = binop_inst(4, MirBinOp.BroadcastAdd, 3, 2)
val extra_use = MirInst(kind: MirInstKind.Copy(LocalId(id: 5), LocalId(id: 3)), span: nil)
val func = test_func([matmul, add, extra_use], MirTerminator.Ret(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, add)
expect(plan.is_some()).to_equal(false)
```

</details>

#### does not fuse non-add broadcast operations

- does not fuse non-add broadcast operations
   - Expected: plan.is_some() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fuse non-add broadcast operations")
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val sub = binop_inst(4, MirBinOp.BroadcastSub, 3, 2)
val func = test_func([matmul, sub], MirTerminator.Ret(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, sub)
expect(plan.is_some()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Cranelift GEMM-add fusion detection.
- Cranelift GEMM-add fusion detection

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c6644e9b8a5d8517db2b5eb776b6baf6f09fadf9b2c9648bf9e6908e739d72b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c6644e9b8a5d8517db2b5eb776b6baf6f09fadf9b2c9648bf9e6908e739d72b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c6644e9b8a5d8517db2b5eb776b6baf6f09fadf9b2c9648bf9e6908e739d72b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl
mirror: doc/06_spec/unit/compiler/backend/cranelift_gemm_fusion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/cranelift_gemm_fusion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/cranelift_gemm_fusion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects adjacent MatMul consumed once by BroadcastAdd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not fuse when the MatMul temp has a second use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/cranelift_gemm_fusion_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not fuse non-add broadcast operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
