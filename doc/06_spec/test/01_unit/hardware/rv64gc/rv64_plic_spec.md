# RV64 PLIC Unit Tests

> Unit tests for Platform-Level Interrupt Controller. PLIC base address: 0xC000000.

<!-- sdn-diagram:id=rv64_plic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_plic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_plic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_plic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 PLIC Unit Tests

Unit tests for Platform-Level Interrupt Controller. PLIC base address: 0xC000000.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-PLIC-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_plic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for Platform-Level Interrupt Controller.
PLIC base address: 0xC000000.

## Scenarios

### Priority

#### set priority for source

1. var plic =  create plic
   - Expected: plic.priorities[1] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 5
expect(plic.priorities[1]).to_equal(5)
```

</details>

#### priority 0 disables source

1. var plic =  create plic
   - Expected: plic.claim(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 0
plic.pending[1] = true
plic.enable[0][1] = true
expect(plic.claim(0)).to_equal(0)
```

</details>

### Enable

#### enable source for context

1. var plic =  create plic
   - Expected: plic.enable[0][1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.enable[0][1] = true
expect(plic.enable[0][1]).to_equal(true)
```

</details>

#### disabled source not visible in claim

1. var plic =  create plic
   - Expected: plic.claim(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 5
plic.pending[1] = true
plic.enable[0][1] = false
expect(plic.claim(0)).to_equal(0)
```

</details>

### Threshold

#### set threshold

1. var plic =  create plic
   - Expected: plic.thresholds[0] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.thresholds[0] = 3
expect(plic.thresholds[0]).to_equal(3)
```

</details>

#### source below threshold not claimed

1. var plic =  create plic
   - Expected: plic.claim(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 2
plic.pending[1] = true
plic.enable[0][1] = true
plic.thresholds[0] = 5
expect(plic.claim(0)).to_equal(0)
```

</details>

### Claim/Complete

#### claim returns highest-priority pending

1. var plic =  create plic
   - Expected: plic.claim(0) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 3
plic.priorities[2] = 5
plic.pending[1] = true
plic.pending[2] = true
plic.enable[0][1] = true
plic.enable[0][2] = true
expect(plic.claim(0)).to_equal(2)
```

</details>

#### claim clears pending

1. var plic =  create plic
2. plic claim
   - Expected: plic.pending[1] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 5
plic.pending[1] = true
plic.enable[0][1] = true
plic.claim(0)
expect(plic.pending[1]).to_equal(false)
```

</details>

#### no pending returns 0

1. var plic =  create plic
   - Expected: plic.claim(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
expect(plic.claim(0)).to_equal(0)
```

</details>

#### priority tie: lower-numbered source wins

1. var plic =  create plic
   - Expected: plic.claim(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 5
plic.priorities[2] = 5
plic.pending[1] = true
plic.pending[2] = true
plic.enable[0][1] = true
plic.enable[0][2] = true
expect(plic.claim(0)).to_equal(1)
```

</details>

### Context Routing

#### different contexts see different enables

1. var plic =  create plic
   - Expected: plic.claim(0) equals `1`
   - Expected: plic.claim(1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var plic = _create_plic(4, 2)
plic.priorities[1] = 5
plic.pending[1] = true
plic.enable[0][1] = true
plic.enable[1][1] = false
expect(plic.claim(0)).to_equal(1)
# Re-trigger for context 1 test
plic.pending[1] = true
expect(plic.claim(1)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
