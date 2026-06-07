# Curve25519 Smalllimb Probe Specification

> <details>

<!-- sdn-diagram:id=curve25519_smalllimb_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=curve25519_smalllimb_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

curve25519_smalllimb_probe_spec -> std
curve25519_smalllimb_probe_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=curve25519_smalllimb_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Curve25519 Smalllimb Probe Specification

## Scenarios

### Curve25519 small-limb probes

#### round-trips a masked arbitrary u-coordinate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x25519_smalllimb_roundtrip_probe(U_TV1_PROBE)).to_equal(x25519_smalllimb_mask_probe(U_TV1_PROBE))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/curve25519_smalllimb_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Curve25519 small-limb probes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
