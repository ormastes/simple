# Trie Facade Native Specification

> <details>

<!-- sdn-diagram:id=trie_facade_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trie_facade_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trie_facade_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trie_facade_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trie Facade Native Specification

## Scenarios

### gc_async_immut PersistentTrie package native backend

#### stores shared-prefix package-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trie = PersistentTrie.empty().set("app", 1).set("apple", 2)

expect(trie.len()).to_equal(2)
expect(trie.get("app")).to_equal(1)
expect(trie.get("apple")).to_equal(2)
```

</details>

#### overwrites package-facade entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trie = PersistentTrie.empty().set("app", 1).set("apple", 2)
val overwritten = trie.set("app", 3)

expect(trie.get("app")).to_equal(1)
expect(overwritten.get("app")).to_equal(3)
expect(overwritten.get("apple")).to_equal(2)
expect(overwritten.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/trie_facade_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut PersistentTrie package native backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
