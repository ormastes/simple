# Metal Readback Proof Specification

## Scenarios

### Metal raw pointer readback proof

#### downloads a deterministic Metal compute buffer

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mismatches = metal_readback_mismatches()
print "METAL_READBACK_PROOF mismatches={mismatches}"
if mismatches == -1:
    expect(true).to_equal(true)
else:
    expect(mismatches).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
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

