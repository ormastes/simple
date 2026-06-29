# Hmac Timing Specification

> <details>

<!-- sdn-diagram:id=hmac_timing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hmac_timing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hmac_timing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hmac_timing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hmac Timing Specification

## Scenarios

### hmac timing

#### single hmac_sha1 call

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [i64] = [0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
                  0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b]
var data: [i64] = [0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65]
val r = hmac_sha1_bytes(key, data)
expect(r.len()).to_equal(20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hmac_timing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hmac timing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
