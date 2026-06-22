# Cbor Diagnostic Negative Offset Guard Specification

> <details>

<!-- sdn-diagram:id=cbor_diagnostic_negative_offset_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_diagnostic_negative_offset_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_diagnostic_negative_offset_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_diagnostic_negative_offset_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Diagnostic Negative Offset Guard Specification

## Scenarios

### CBOR diagnostic negative offset guard

#### rejects negative offsets before diagnostic decoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/common/cbor/utilities.spl") ?? ""
expect(source).to_contain("if offset < 0 or offset >= bytes.len():")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_diagnostic_negative_offset_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CBOR diagnostic negative offset guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
