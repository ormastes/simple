# X25519 Helper Probe Specification

> <details>

<!-- sdn-diagram:id=x25519_helper_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x25519_helper_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x25519_helper_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x25519_helper_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519 Helper Probe Specification

## Scenarios

### x25519 helper portable probe

#### records scalar and public key widths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(X25519_A_HEX.len()).to_equal(64)
expect(X25519_A_PUBLIC_HEX.len()).to_equal(64)
```

</details>

#### records shared secret width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(X25519_SHARED_HEX.len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/x25519_helper_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x25519 helper portable probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
