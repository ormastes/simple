# Metal Readback Proof Specification

> <details>

<!-- sdn-diagram:id=metal_readback_proof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metal_readback_proof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metal_readback_proof_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metal_readback_proof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Readback Proof Specification

## Scenarios

### Metal raw pointer readback proof

#### downloads a deterministic Metal compute buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mismatches = metal_readback_mismatches()
print "METAL_READBACK_PROOF mismatches={mismatches}"
if mismatches == -1:
    expect(mismatches).to_equal(-1)
else:
    expect(mismatches).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/metal_readback_proof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal raw pointer readback proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
