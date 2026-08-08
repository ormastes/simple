# Reader Smt Specification

> <details>

<!-- sdn-diagram:id=reader_smt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reader_smt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reader_smt_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reader_smt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reader Smt Specification

## Scenarios

### semihost SMT JSON loading

#### rejects malformed string ids before integer parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smt_json_id_end("x", 0)).to_equal(-1)
```

</details>

#### returns the end offset for numeric string ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smt_json_id_end("123,", 0)).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/semihost/reader_smt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semihost SMT JSON loading

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
