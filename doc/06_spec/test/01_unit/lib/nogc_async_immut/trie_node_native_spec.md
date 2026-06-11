# Trie Node Native Specification

> <details>

<!-- sdn-diagram:id=trie_node_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trie_node_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trie_node_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trie_node_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trie Node Native Specification

## Scenarios

### nogc_async_immut trie node native backend

#### stores and retrieves shared-prefix nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = trie_set(nil, "app", 1, 0)
val next = trie_set(root, "apple", 2, 0)

expect(trie_get(next, "app", 0)).to_equal(1)
expect(trie_get(next, "apple", 0)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_immut/trie_node_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_immut trie node native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
