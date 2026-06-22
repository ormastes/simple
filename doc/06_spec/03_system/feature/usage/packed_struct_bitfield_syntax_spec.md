# Packed Struct Bitfield Syntax Specification

> <details>

<!-- sdn-diagram:id=packed_struct_bitfield_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=packed_struct_bitfield_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

packed_struct_bitfield_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=packed_struct_bitfield_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Struct Bitfield Syntax Specification

## Scenarios

### FR-DRIVER-0003 packed struct bitfield syntax

#### documents requested native syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(requested_syntax).to_contain("@packed")
expect(requested_syntax).to_contain("u16:4")
```

</details>

#### documents current implementation boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(current_status).to_equal("parser diagnostic only")
expect(fallback).to_start_with("bitfield")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/03_system/feature/usage/packed_struct_bitfield_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-DRIVER-0003 packed struct bitfield syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
