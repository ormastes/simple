# Testing Attributes Facade Specification

> <details>

<!-- sdn-diagram:id=testing_attributes_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=testing_attributes_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

testing_attributes_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=testing_attributes_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Testing Attributes Facade Specification

## Scenarios

### nogc_async_mut testing attributes facade

#### re-exports test metadata and validation helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = TestMeta(name: "slow case", timeout_ms: 5000, retry_count: 2, tags: ["slow"], skip_reason: nil, is_flaky: true)
expect(meta.name).to_equal("slow case")
expect(meta.tags[0]).to_equal("slow")
expect(meta.is_flaky).to_equal(true)
expect(validate_timeout(5000)).to_equal(true)
expect(validate_timeout(0)).to_equal(false)
expect(validate_retry(3)).to_equal(true)
expect(validate_retry(11)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/testing/testing_attributes_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut testing attributes facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
