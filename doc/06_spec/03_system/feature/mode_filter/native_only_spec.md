# Native-Only Mode Tests

> Tests restricted to native compiled mode via `@mode: native` annotation.

<!-- sdn-diagram:id=native_only_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_only_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_only_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_only_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native-Only Mode Tests

Tests restricted to native compiled mode via `@mode: native` annotation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing Framework |
| Status | Active |
| Source | `test/03_system/feature/mode_filter/native_only_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests restricted to native compiled mode via `@mode: native` annotation.

## Scenarios

### Native-only features

#### runs compiled code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
