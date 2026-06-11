# Group Specification

> Group construction, membership check, and nested group expansion.

<!-- sdn-diagram:id=group_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=group_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

group_spec -> std
group_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=group_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Group Specification

Group construction, membership check, and nested group expansion.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/group_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Group construction, membership check, and nested group expansion.

## Scenarios

### Group

### construction + membership

#### AC-1: flat group reports its members

1. expect group has member
2. expect group has member


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = id_path_intern("id.group.dev")
val alice = id_path_intern("id.user.alice")
val bob = id_path_intern("id.user.bob")
val g = GroupDecl(id_path: dev, members: [alice, bob])
expect group_has_member(g, alice) to_equal true
expect group_has_member(g, bob) to_equal true
```

</details>

#### AC-1: non-member is rejected

1. expect group has member


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = id_path_intern("id.group.dev")
val alice = id_path_intern("id.user.alice")
val eve = id_path_intern("id.user.eve")
val g = GroupDecl(id_path: dev, members: [alice])
expect group_has_member(g, eve) to_equal false
```

</details>

### nested expansion

#### AC-1: nested groups are transitively expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = id_path_intern("id.group.eng")
val dev = id_path_intern("id.group.dev")
val qa = id_path_intern("id.group.qa")
val alice = id_path_intern("id.user.alice")
val bob = id_path_intern("id.user.bob")
val g_dev = GroupDecl(id_path: dev, members: [alice])
val g_qa = GroupDecl(id_path: qa, members: [bob])
val g_eng = GroupDecl(id_path: eng, members: [dev, qa])
val universe = [g_dev, g_qa, g_eng]
val leaves = group_expand_nested(g_eng, universe)
expect leaves to_contain alice
expect leaves to_contain bob
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
