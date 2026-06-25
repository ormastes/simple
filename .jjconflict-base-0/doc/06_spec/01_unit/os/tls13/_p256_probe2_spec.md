# P256 Probe2 Specification

> 1. s push

<!-- sdn-diagram:id=_p256_probe2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_p256_probe2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_p256_probe2_spec -> std
_p256_probe2_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_p256_probe2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Probe2 Specification

## Scenarios

### probe

#### smoke len inline

1. s push
2. s push
   - Expected: out.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s: [u8] = []
var i: u64 = 0u64
while i < 31u64:
    s.push(0x00u8)
    i = i + 1u64
s.push(0x01u8)
val out = p256_keypair_pub(s)
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### smoke len fn-result-stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: [u8] = _cs()
val out = p256_keypair_pub(s)
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### smoke len fn-direct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = p256_keypair_pub(_cs())
expect(out.len().to_u64()).to_equal(65u64)
```

</details>

#### trivial fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: [u8] = _trivial()
expect(s.len().to_u64()).to_equal(1u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/_p256_probe2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
