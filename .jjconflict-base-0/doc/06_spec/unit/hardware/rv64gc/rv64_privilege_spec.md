# RV64 Privilege Mode Unit Tests

> Unit tests for M/S/U privilege mode transitions, trap delegation, CSR access control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Privilege Mode Unit Tests

Unit tests for M/S/U privilege mode transitions, trap delegation, CSR access control.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-PRIVILEGE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_privilege_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for M/S/U privilege mode transitions, trap delegation, CSR access control.

## Scenarios

### M-to-S Transition via MRET

#### MRET with MPP=S transitions to S-mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- MRET with MPP=S transitions to S-mode
   - Expected: p.mode equals `PRIV_S`
   - Expected: pc equals `0x80002000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MRET with MPP=S transitions to S-mode")
var p = _create_priv()
p.mstatus = 1 << MSTATUS_MPP_SHIFT  # MPP=01 (S)
p.mepc = 0x80002000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_S)
expect(pc).to_equal(0x80002000)
```

</details>

#### MRET with MPP=U transitions to U-mode

- MRET with MPP=U transitions to U-mode
   - Expected: p.mode equals `PRIV_U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MRET with MPP=U transitions to U-mode")
var p = _create_priv()
p.mstatus = 0  # MPP=00 (U)
p.mepc = 0x10000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_U)
```

</details>

### S-to-U Transition via SRET

#### SRET with SPP=0 transitions to U-mode

- SRET with SPP=0 transitions to U-mode
   - Expected: p.mode equals `PRIV_U`
   - Expected: pc equals `0x10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SRET with SPP=0 transitions to U-mode")
var p = _create_priv()
p.mode = PRIV_S
p.mstatus = 0  # SPP=0 (U)
p.sepc = 0x10000
val pc = p.sret()
expect(p.mode).to_equal(PRIV_U)
expect(pc).to_equal(0x10000)
```

</details>

#### SRET with SPP=1 transitions to S-mode

- SRET with SPP=1 transitions to S-mode
   - Expected: p.mode equals `PRIV_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SRET with SPP=1 transitions to S-mode")
var p = _create_priv()
p.mode = PRIV_S
p.mstatus = MSTATUS_SPP  # SPP=1 (S)
p.sepc = 0x80003000
val pc = p.sret()
expect(p.mode).to_equal(PRIV_S)
```

</details>

### Trap Delegation

#### exception delegated when medeleg bit set

- exception delegated when medeleg bit set
   - Expected: p.should_delegate_exception(8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exception delegated when medeleg bit set")
var p = _create_priv()
p.medeleg = 1 << 8  # Delegate ecall-from-U
expect(p.should_delegate_exception(8)).to_equal(true)
```

</details>

#### exception not delegated when medeleg bit clear

- exception not delegated when medeleg bit clear
   - Expected: p.should_delegate_exception(8) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exception not delegated when medeleg bit clear")
var p = _create_priv()
p.medeleg = 0
expect(p.should_delegate_exception(8)).to_equal(false)
```

</details>

#### interrupt delegated when mideleg bit set

- interrupt delegated when mideleg bit set
   - Expected: p.should_delegate_interrupt(5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt delegated when mideleg bit set")
var p = _create_priv()
p.mideleg = 1 << 5  # Delegate S-mode timer
expect(p.should_delegate_interrupt(5)).to_equal(true)
```

</details>

#### interrupt not delegated when mideleg bit clear

- interrupt not delegated when mideleg bit clear
   - Expected: p.should_delegate_interrupt(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interrupt not delegated when mideleg bit clear")
var p = _create_priv()
p.mideleg = 0
expect(p.should_delegate_interrupt(5)).to_equal(false)
```

</details>

### CSR Access Per Mode

#### M-mode can access M-mode CSRs (0x3xx)

- M-mode can access M-mode CSRs (0x3xx)
   - Expected: p.can_access_csr(0x300) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("M-mode can access M-mode CSRs (0x3xx)")
var p = _create_priv()
p.mode = PRIV_M
expect(p.can_access_csr(0x300)).to_equal(true)
```

</details>

#### S-mode cannot access M-mode CSRs

- S-mode cannot access M-mode CSRs
   - Expected: p.can_access_csr(0x300) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("S-mode cannot access M-mode CSRs")
var p = _create_priv()
p.mode = PRIV_S
expect(p.can_access_csr(0x300)).to_equal(false)
```

</details>

#### S-mode can access S-mode CSRs (0x1xx)

- S-mode can access S-mode CSRs (0x1xx)
   - Expected: p.can_access_csr(0x100) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("S-mode can access S-mode CSRs (0x1xx)")
var p = _create_priv()
p.mode = PRIV_S
expect(p.can_access_csr(0x100)).to_equal(true)
```

</details>

#### U-mode cannot access S-mode CSRs

- U-mode cannot access S-mode CSRs
   - Expected: p.can_access_csr(0x100) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U-mode cannot access S-mode CSRs")
var p = _create_priv()
p.mode = PRIV_U
expect(p.can_access_csr(0x100)).to_equal(false)
```

</details>

#### U-mode can access U-mode CSRs (0x0xx)

- U-mode can access U-mode CSRs (0x0xx)
   - Expected: p.can_access_csr(0x001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U-mode can access U-mode CSRs (0x0xx)")
var p = _create_priv()
p.mode = PRIV_U
expect(p.can_access_csr(0x001)).to_equal(true)
```

</details>

#### M-mode can access all privilege levels

- M-mode can access all privilege levels
   - Expected: p.can_access_csr(0x001) is true
   - Expected: p.can_access_csr(0x100) is true
   - Expected: p.can_access_csr(0x300) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("M-mode can access all privilege levels")
var p = _create_priv()
p.mode = PRIV_M
expect(p.can_access_csr(0x001)).to_equal(true)
expect(p.can_access_csr(0x100)).to_equal(true)
expect(p.can_access_csr(0x300)).to_equal(true)
```

</details>

### MPP/SPP Field Encoding

#### MPP: 0=U, 1=S, 3=M

- MPP: 0=U, 1=S, 3=M
   - Expected: p.mode equals `PRIV_M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MPP: 0=U, 1=S, 3=M")
var p = _create_priv()
# Set MPP=M (11)
p.mstatus = 3 << MSTATUS_MPP_SHIFT
p.mepc = 0x80000000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_M)
```

</details>

#### SPP: 0=U, 1=S

- SPP: 0=U, 1=S
   - Expected: p.mode equals `PRIV_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SPP: 0=U, 1=S")
var p = _create_priv()
p.mode = PRIV_S
p.mstatus = MSTATUS_SPP
p.sepc = 0x80001000
val pc = p.sret()
expect(p.mode).to_equal(PRIV_S)
```

</details>

### WFI in U-Mode

#### WFI raises exception when TW=1

- WFI raises exception when TW=1
   - Expected: tw_set and p.mode == PRIV_U is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("WFI raises exception when TW=1")
var p = _create_priv()
p.mode = PRIV_U
p.mstatus = MSTATUS_TW
val tw_set = (p.mstatus and MSTATUS_TW) != 0
expect(tw_set and p.mode == PRIV_U).to_equal(true)
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

- Canonical SPipe generation for source `e8e8a092ca33fc5a32a37f200c741c53c21cfc2d7ee9698a4ac3209f0e9d74e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8e8a092ca33fc5a32a37f200c741c53c21cfc2d7ee9698a4ac3209f0e9d74e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8e8a092ca33fc5a32a37f200c741c53c21cfc2d7ee9698a4ac3209f0e9d74e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv64gc/rv64_privilege_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_privilege_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_privilege_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_privilege_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_privilege_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MRET with MPP=S transitions to S-mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_privilege_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MRET with MPP=U transitions to U-mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_privilege_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SRET with SPP=0 transitions to U-mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
