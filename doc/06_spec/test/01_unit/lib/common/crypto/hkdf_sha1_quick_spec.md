# Hkdf Sha1 Quick Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha1_quick_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha1_quick_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha1_quick_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha1_quick_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha1 Quick Specification

## Scenarios

### hkdf sha1 timing

#### extract is fast

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha1(_salt(), _ikm())
expect(prk.len()).to_equal(20)
```

</details>

#### expand L=42 is fast enough

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha1(_salt(), _ikm())
val okm = hkdf_expand_sha1(prk, _info(), 42)
expect(okm.len()).to_equal(42)
expect(bytes_to_hex(okm)).to_equal(
    "085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2c22e422478d305f3f896"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha1_quick_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hkdf sha1 timing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
