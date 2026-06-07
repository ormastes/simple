# RV64 Privilege Mode Unit Tests

> Unit tests for M/S/U privilege mode transitions, trap delegation, CSR access control.

<!-- sdn-diagram:id=rv64_privilege_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_privilege_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_privilege_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_privilege_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/hardware/rv64gc/rv64_privilege_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for M/S/U privilege mode transitions, trap delegation, CSR access control.

## Scenarios

### M-to-S Transition via MRET

#### MRET with MPP=S transitions to S-mode

1. var p =  create priv
2. p mstatus = 1 << MSTATUS MPP SHIFT  # MPP=01
   - Expected: p.mode equals `PRIV_S`
   - Expected: pc equals `0x80002000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mstatus = 1 << MSTATUS_MPP_SHIFT  # MPP=01 (S)
p.mepc = 0x80002000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_S)
expect(pc).to_equal(0x80002000)
```

</details>

#### MRET with MPP=U transitions to U-mode

1. var p =  create priv
2. p mstatus = 0  # MPP=00
   - Expected: p.mode equals `PRIV_U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mstatus = 0  # MPP=00 (U)
p.mepc = 0x10000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_U)
```

</details>

### S-to-U Transition via SRET

#### SRET with SPP=0 transitions to U-mode

1. var p =  create priv
2. p mstatus = 0  # SPP=0
   - Expected: p.mode equals `PRIV_U`
   - Expected: pc equals `0x10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var p =  create priv
2. p mstatus = MSTATUS SPP  # SPP=1
   - Expected: p.mode equals `PRIV_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var p =  create priv
   - Expected: p.should_delegate_exception(8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.medeleg = 1 << 8  # Delegate ecall-from-U
expect(p.should_delegate_exception(8)).to_equal(true)
```

</details>

#### exception not delegated when medeleg bit clear

1. var p =  create priv
   - Expected: p.should_delegate_exception(8) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.medeleg = 0
expect(p.should_delegate_exception(8)).to_equal(false)
```

</details>

#### interrupt delegated when mideleg bit set

1. var p =  create priv
   - Expected: p.should_delegate_interrupt(5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mideleg = 1 << 5  # Delegate S-mode timer
expect(p.should_delegate_interrupt(5)).to_equal(true)
```

</details>

#### interrupt not delegated when mideleg bit clear

1. var p =  create priv
   - Expected: p.should_delegate_interrupt(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mideleg = 0
expect(p.should_delegate_interrupt(5)).to_equal(false)
```

</details>

### CSR Access Per Mode

#### M-mode can access M-mode CSRs (0x3xx)

1. var p =  create priv
   - Expected: p.can_access_csr(0x300) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_M
expect(p.can_access_csr(0x300)).to_equal(true)
```

</details>

#### S-mode cannot access M-mode CSRs

1. var p =  create priv
   - Expected: p.can_access_csr(0x300) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_S
expect(p.can_access_csr(0x300)).to_equal(false)
```

</details>

#### S-mode can access S-mode CSRs (0x1xx)

1. var p =  create priv
   - Expected: p.can_access_csr(0x100) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_S
expect(p.can_access_csr(0x100)).to_equal(true)
```

</details>

#### U-mode cannot access S-mode CSRs

1. var p =  create priv
   - Expected: p.can_access_csr(0x100) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_U
expect(p.can_access_csr(0x100)).to_equal(false)
```

</details>

#### U-mode can access U-mode CSRs (0x0xx)

1. var p =  create priv
   - Expected: p.can_access_csr(0x001) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_U
expect(p.can_access_csr(0x001)).to_equal(true)
```

</details>

#### M-mode can access all privilege levels

1. var p =  create priv
   - Expected: p.can_access_csr(0x001) is true
   - Expected: p.can_access_csr(0x100) is true
   - Expected: p.can_access_csr(0x300) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
p.mode = PRIV_M
expect(p.can_access_csr(0x001)).to_equal(true)
expect(p.can_access_csr(0x100)).to_equal(true)
expect(p.can_access_csr(0x300)).to_equal(true)
```

</details>

### MPP/SPP Field Encoding

#### MPP: 0=U, 1=S, 3=M

1. var p =  create priv
   - Expected: p.mode equals `PRIV_M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = _create_priv()
# Set MPP=M (11)
p.mstatus = 3 << MSTATUS_MPP_SHIFT
p.mepc = 0x80000000
val pc = p.mret()
expect(p.mode).to_equal(PRIV_M)
```

</details>

#### SPP: 0=U, 1=S

1. var p =  create priv
   - Expected: p.mode equals `PRIV_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var p =  create priv
   - Expected: tw_set and p.mode == PRIV_U is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
