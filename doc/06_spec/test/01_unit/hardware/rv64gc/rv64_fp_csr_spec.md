# RV64 FP CSR Unit Tests

> Unit tests for floating-point CSRs: fcsr, fflags, frm.

<!-- sdn-diagram:id=rv64_fp_csr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_csr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_csr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_csr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 FP CSR Unit Tests

Unit tests for floating-point CSRs: fcsr, fflags, frm.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-CSR-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_csr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for floating-point CSRs: fcsr, fflags, frm.

## Scenarios

### FCSR Read/Write

#### fcsr initially zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr = _FpCsr(fcsr: 0)
expect(csr.fcsr).to_equal(0)
```

</details>

#### write and read full fcsr

1. var csr =  FpCsr
   - Expected: csr.fcsr and 0xFF equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.fcsr = 0xFF
expect(csr.fcsr and 0xFF).to_equal(0xFF)
```

</details>

#### fcsr only uses lower 8 bits (frm + fflags)

1. var csr =  FpCsr
   - Expected: csr.fflags() equals `0x1F`
   - Expected: csr.frm() equals `0x7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0xFF)
expect(csr.fflags()).to_equal(0x1F)
expect(csr.frm()).to_equal(0x7)
```

</details>

### FFlags Individual Flags

#### NX (inexact) flag

1. var csr =  FpCsr
2. csr accum flags
   - Expected: csr.fflags() and FP_FLAG_NX equals `FP_FLAG_NX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_NX)
expect(csr.fflags() and FP_FLAG_NX).to_equal(FP_FLAG_NX)
```

</details>

#### UF (underflow) flag

1. var csr =  FpCsr
2. csr accum flags
   - Expected: csr.fflags() and FP_FLAG_UF equals `FP_FLAG_UF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_UF)
expect(csr.fflags() and FP_FLAG_UF).to_equal(FP_FLAG_UF)
```

</details>

#### OF (overflow) flag

1. var csr =  FpCsr
2. csr accum flags
   - Expected: csr.fflags() and FP_FLAG_OF equals `FP_FLAG_OF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_OF)
expect(csr.fflags() and FP_FLAG_OF).to_equal(FP_FLAG_OF)
```

</details>

#### DZ (divide by zero) flag

1. var csr =  FpCsr
2. csr accum flags
   - Expected: csr.fflags() and FP_FLAG_DZ equals `FP_FLAG_DZ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_DZ)
expect(csr.fflags() and FP_FLAG_DZ).to_equal(FP_FLAG_DZ)
```

</details>

#### NV (invalid operation) flag

1. var csr =  FpCsr
2. csr accum flags
   - Expected: csr.fflags() and FP_FLAG_NV equals `FP_FLAG_NV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_NV)
expect(csr.fflags() and FP_FLAG_NV).to_equal(FP_FLAG_NV)
```

</details>

### FRM Rounding Modes

#### RNE (round to nearest, ties to even) = 0

1. var csr =  FpCsr
2. csr set frm
   - Expected: csr.frm() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(0)
expect(csr.frm()).to_equal(0)
```

</details>

#### RTZ (round toward zero) = 1

1. var csr =  FpCsr
2. csr set frm
   - Expected: csr.frm() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(1)
expect(csr.frm()).to_equal(1)
```

</details>

#### RDN (round down) = 2

1. var csr =  FpCsr
2. csr set frm
   - Expected: csr.frm() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(2)
expect(csr.frm()).to_equal(2)
```

</details>

#### RUP (round up) = 3

1. var csr =  FpCsr
2. csr set frm
   - Expected: csr.frm() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(3)
expect(csr.frm()).to_equal(3)
```

</details>

#### RMM (round to nearest, ties to max magnitude) = 4

1. var csr =  FpCsr
2. csr set frm
   - Expected: csr.frm() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(4)
expect(csr.frm()).to_equal(4)
```

</details>

### Exception Accumulation

#### flags OR together (accumulate)

1. var csr =  FpCsr
2. csr accum flags
3. csr accum flags
   - Expected: csr.fflags() equals `FP_FLAG_NX or FP_FLAG_OF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.accum_flags(FP_FLAG_NX)
csr.accum_flags(FP_FLAG_OF)
expect(csr.fflags()).to_equal(FP_FLAG_NX or FP_FLAG_OF)
```

</details>

#### setting fflags preserves frm

1. var csr =  FpCsr
2. csr set frm
3. csr set fflags
   - Expected: csr.frm() equals `3`
   - Expected: csr.fflags() equals `0x1F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0)
csr.set_frm(3)
csr.set_fflags(0x1F)
expect(csr.frm()).to_equal(3)
expect(csr.fflags()).to_equal(0x1F)
```

</details>

#### reset clears all

1. var csr =  FpCsr
2. csr clear all
   - Expected: csr.fcsr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _FpCsr(fcsr: 0xFF)
csr.clear_all()
expect(csr.fcsr).to_equal(0)
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
