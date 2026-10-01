# RV64 Pipeline Control Unit Tests

> Unit tests for 64-bit pipeline hazard detection and data forwarding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Pipeline Control Unit Tests

Unit tests for 64-bit pipeline hazard detection and data forwarding.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-PIPELINE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 64-bit pipeline hazard detection and data forwarding.

## Scenarios

### Load-Use Hazard Detection

#### LD followed by dependent ALU detects hazard

- LD followed by dependent ALU detects hazard
   - Expected: hazard is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LD followed by dependent ALU detects hazard")
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 10, id_rs2: 0
)
expect(hazard).to_equal(true)
```

</details>

#### LD followed by independent ALU has no hazard

- LD followed by independent ALU has no hazard
   - Expected: hazard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LD followed by independent ALU has no hazard")
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 11, id_rs2: 12
)
expect(hazard).to_equal(false)
```

</details>

#### non-load instruction has no load-use hazard

- non-load instruction has no load-use hazard
   - Expected: hazard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-load instruction has no load-use hazard")
val hazard = detect_load_use_hazard(
    ex_is_load: false, ex_rd: 10,
    id_rs1: 10, id_rs2: 0
)
expect(hazard).to_equal(false)
```

</details>

#### hazard on rs2 dependency

- hazard on rs2 dependency
   - Expected: hazard is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hazard on rs2 dependency")
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 0, id_rs2: 10
)
expect(hazard).to_equal(true)
```

</details>

#### no hazard when ex_rd is x0

- no hazard when ex_rd is x0
   - Expected: hazard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no hazard when ex_rd is x0")
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 0,
    id_rs1: 0, id_rs2: 0
)
expect(hazard).to_equal(false)
```

</details>

#### LW also triggers hazard

- LW also triggers hazard
   - Expected: hazard is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LW also triggers hazard")
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 5,
    id_rs1: 5, id_rs2: 0
)
expect(hazard).to_equal(true)
```

</details>

### Data Forwarding

#### forward from EX stage to rs1

- forward from EX stage to rs1
   - Expected: fwd equals `ForwardSrc.FromEx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forward from EX stage to rs1")
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd).to_equal(ForwardSrc.FromEx)
```

</details>

#### forward from MEM stage to rs1

- forward from MEM stage to rs1
   - Expected: fwd equals `ForwardSrc.FromMem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forward from MEM stage to rs1")
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 0, ex_write_en: false,
    mem_rd: 10, mem_write_en: true
)
expect(fwd).to_equal(ForwardSrc.FromMem)
```

</details>

#### no forwarding when no match

- no forwarding when no match
   - Expected: fwd equals `ForwardSrc.RegFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no forwarding when no match")
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 11, ex_write_en: true,
    mem_rd: 12, mem_write_en: true
)
expect(fwd).to_equal(ForwardSrc.RegFile)
```

</details>

#### no forwarding when rd is x0

- no forwarding when rd is x0
   - Expected: fwd equals `ForwardSrc.RegFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no forwarding when rd is x0")
val fwd = resolve_forward_rs1(
    id_rs1: 0,
    ex_rd: 0, ex_write_en: true,
    mem_rd: 0, mem_write_en: true
)
expect(fwd).to_equal(ForwardSrc.RegFile)
```

</details>

#### EX has priority over MEM

- EX has priority over MEM
   - Expected: fwd equals `ForwardSrc.FromEx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EX has priority over MEM")
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 10, mem_write_en: true
)
expect(fwd).to_equal(ForwardSrc.FromEx)
```

</details>

### Pipeline Control

#### stall on load-use hazard

- stall on load-use hazard
   - Expected: ctrl.stall is true
   - Expected: ctrl.flush is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stall on load-use hazard")
val ctrl = compute_pipeline_control(
    load_use_hazard: true, branch_taken: false
)
expect(ctrl.stall).to_equal(true)
expect(ctrl.flush).to_equal(false)
```

</details>

#### flush on branch taken

- flush on branch taken
   - Expected: ctrl.stall is false
   - Expected: ctrl.flush is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flush on branch taken")
val ctrl = compute_pipeline_control(
    load_use_hazard: false, branch_taken: true
)
expect(ctrl.stall).to_equal(false)
expect(ctrl.flush).to_equal(true)
```

</details>

#### no stall or flush in normal operation

- no stall or flush in normal operation
   - Expected: ctrl.stall is false
   - Expected: ctrl.flush is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no stall or flush in normal operation")
val ctrl = compute_pipeline_control(
    load_use_hazard: false, branch_taken: false
)
expect(ctrl.stall).to_equal(false)
expect(ctrl.flush).to_equal(false)
```

</details>

### 64-bit Forwarding Paths

#### LD creates 64-bit forwarding path

- LD creates 64-bit forwarding path
   - Expected: fwd equals `ForwardSrc.FromEx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LD creates 64-bit forwarding path")
val fwd = resolve_forward_rs2(
    id_rs2: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd).to_equal(ForwardSrc.FromEx)
```

</details>

#### SD with forwarded store data

- SD with forwarded store data
   - Expected: fwd equals `ForwardSrc.FromEx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SD with forwarded store data")
val fwd = resolve_forward_rs2(
    id_rs2: 11,
    ex_rd: 11, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd).to_equal(ForwardSrc.FromEx)
```

</details>

#### double forwarding: both rs1 and rs2 from different stages

- double forwarding: both rs1 and rs2 from different stages
   - Expected: fwd1 equals `ForwardSrc.FromEx`
   - Expected: fwd2 equals `ForwardSrc.FromMem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("double forwarding: both rs1 and rs2 from different stages")
val fwd1 = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
val fwd2 = resolve_forward_rs2(
    id_rs2: 11,
    ex_rd: 0, ex_write_en: false,
    mem_rd: 11, mem_write_en: true
)
expect(fwd1).to_equal(ForwardSrc.FromEx)
expect(fwd2).to_equal(ForwardSrc.FromMem)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `f1d3accc75664b60a577d5a1ba6c14d87bb10d440c12714357d93ca7119b9170`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1d3accc75664b60a577d5a1ba6c14d87bb10d440c12714357d93ca7119b9170`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1d3accc75664b60a577d5a1ba6c14d87bb10d440c12714357d93ca7119b9170`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv64gc/rv64_pipeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv64gc/rv64_pipeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv64gc/rv64_pipeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LD followed by dependent ALU detects hazard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LD followed by independent ALU has no hazard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'non-load instruction has no load-use hazard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
