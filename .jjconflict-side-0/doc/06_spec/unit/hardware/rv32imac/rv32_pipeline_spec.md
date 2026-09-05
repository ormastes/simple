# RV32 Pipeline Control Unit Tests

> Unit tests for pipeline hazard detection, forwarding, and control signals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Pipeline Control Unit Tests

Unit tests for pipeline hazard detection, forwarding, and control signals.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-PIPELINE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/unit/hardware/rv32imac/rv32_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for pipeline hazard detection, forwarding, and control signals.

## Scenarios

### Load-Use Hazard Detection

#### detects hazard on rs1

- detects hazard on rs1
   - Expected: detect_load_use_hazard(5, 0, 5, MemOp.Load, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects hazard on rs1")
expect(detect_load_use_hazard(5, 0, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### detects hazard on rs2

- detects hazard on rs2
   - Expected: detect_load_use_hazard(0, 5, 5, MemOp.Load, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects hazard on rs2")
expect(detect_load_use_hazard(0, 5, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### no hazard for non-load

- no hazard for non-load
   - Expected: detect_load_use_hazard(5, 0, 5, MemOp.Store, true) is false
   - Expected: detect_load_use_hazard(5, 0, 5, MemOp.None, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no hazard for non-load")
expect(detect_load_use_hazard(5, 0, 5, MemOp.Store, true)).to_equal(false)
expect(detect_load_use_hazard(5, 0, 5, MemOp.None, true)).to_equal(false)
```

</details>

#### no hazard when EX invalid

- no hazard when EX invalid
   - Expected: detect_load_use_hazard(5, 0, 5, MemOp.Load, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no hazard when EX invalid")
expect(detect_load_use_hazard(5, 0, 5, MemOp.Load, false)).to_equal(false)
```

</details>

#### no hazard when rd is x0

- no hazard when rd is x0
   - Expected: detect_load_use_hazard(0, 3, 0, MemOp.Load, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no hazard when rd is x0")
expect(detect_load_use_hazard(0, 3, 0, MemOp.Load, true)).to_equal(false)
```

</details>

#### no hazard when no register match

- no hazard when no register match
   - Expected: detect_load_use_hazard(3, 4, 5, MemOp.Load, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no hazard when no register match")
expect(detect_load_use_hazard(3, 4, 5, MemOp.Load, true)).to_equal(false)
```

</details>

### Data Forwarding

#### forwards from EX stage when match

- forwards from EX stage when match
   - Expected: resolve_forward_rs1(5, 5, true, 0, false) equals `ForwardSrc.ExStage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards from EX stage when match")
expect(resolve_forward_rs1(5, 5, true, 0, false)).to_equal(ForwardSrc.ExStage)
```

</details>

#### forwards from MEM stage when EX doesn't match

- forwards from MEM stage when EX doesn't match
   - Expected: resolve_forward_rs1(5, 3, true, 5, true) equals `ForwardSrc.MemStage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards from MEM stage when EX doesn't match")
expect(resolve_forward_rs1(5, 3, true, 5, true)).to_equal(ForwardSrc.MemStage)
```

</details>

#### uses regfile when no match

- uses regfile when no match
   - Expected: resolve_forward_rs1(5, 3, true, 4, true) equals `ForwardSrc.RegFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses regfile when no match")
expect(resolve_forward_rs1(5, 3, true, 4, true)).to_equal(ForwardSrc.RegFile)
```

</details>

#### x0 always from regfile

- x0 always from regfile
   - Expected: resolve_forward_rs1(0, 0, true, 0, true) equals `ForwardSrc.RegFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x0 always from regfile")
expect(resolve_forward_rs1(0, 0, true, 0, true)).to_equal(ForwardSrc.RegFile)
```

</details>

#### EX has priority over MEM

- EX has priority over MEM
   - Expected: resolve_forward_rs1(5, 5, true, 5, true) equals `ForwardSrc.ExStage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EX has priority over MEM")
expect(resolve_forward_rs1(5, 5, true, 5, true)).to_equal(ForwardSrc.ExStage)
```

</details>

### Pipeline Control Signals

#### normal operation - no stalls or flushes

- normal operation - no stalls or flushes
   - Expected: ctrl.stall_if is false
   - Expected: ctrl.stall_id is false
   - Expected: ctrl.flush_if is false
   - Expected: ctrl.flush_id is false
   - Expected: ctrl.flush_ex is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normal operation - no stalls or flushes")
val ctrl = compute_pipeline_control(false, false, false)
expect(ctrl.stall_if).to_equal(false)
expect(ctrl.stall_id).to_equal(false)
expect(ctrl.flush_if).to_equal(false)
expect(ctrl.flush_id).to_equal(false)
expect(ctrl.flush_ex).to_equal(false)
```

</details>

#### load-use: stalls IF/ID, flushes EX

- load-use: stalls IF/ID, flushes EX
   - Expected: ctrl.stall_if is true
   - Expected: ctrl.stall_id is true
   - Expected: ctrl.flush_ex is true
   - Expected: ctrl.flush_if is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load-use: stalls IF/ID, flushes EX")
val ctrl = compute_pipeline_control(true, false, false)
expect(ctrl.stall_if).to_equal(true)
expect(ctrl.stall_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
expect(ctrl.flush_if).to_equal(false)
```

</details>

#### branch taken: flushes IF/ID

- branch taken: flushes IF/ID
   - Expected: ctrl.flush_if is true
   - Expected: ctrl.flush_id is true
   - Expected: ctrl.stall_if is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branch taken: flushes IF/ID")
val ctrl = compute_pipeline_control(false, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
expect(ctrl.stall_if).to_equal(false)
```

</details>

#### trap: flushes everything

- trap: flushes everything
   - Expected: ctrl.flush_if is true
   - Expected: ctrl.flush_id is true
   - Expected: ctrl.flush_ex is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trap: flushes everything")
val ctrl = compute_pipeline_control(false, false, true)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
```

</details>

#### branch overrides load-use stall

- branch overrides load-use stall
   - Expected: ctrl.flush_if is true
   - Expected: ctrl.stall_if is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("branch overrides load-use stall")
val ctrl = compute_pipeline_control(true, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.stall_if).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `63448166445e976aa59cc8409239efc658360d8083af6f770579853e54583b4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63448166445e976aa59cc8409239efc658360d8083af6f770579853e54583b4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63448166445e976aa59cc8409239efc658360d8083af6f770579853e54583b4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv32imac/rv32_pipeline_spec.spl
mirror: doc/06_spec/unit/hardware/rv32imac/rv32_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv32imac/rv32_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv32imac/rv32_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv32imac/rv32_pipeline_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects hazard on rs1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv32imac/rv32_pipeline_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects hazard on rs2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv32imac/rv32_pipeline_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no hazard for non-load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
