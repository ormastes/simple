# IdPath Specification

> Exercises `IdPath` intern table, prefix match, subdivide, and segment validation

<!-- sdn-diagram:id=id_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=id_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

id_path_spec -> std
id_path_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=id_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IdPath Specification

Exercises `IdPath` intern table, prefix match, subdivide, and segment validation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/id_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `IdPath` intern table, prefix match, subdivide, and segment validation
defined in Phase 3 architecture (`src/lib/common/privilege/id_path.spl`).

## Scenarios

### IdPath

### intern

#### AC-1: returns identical intern_id for identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = id_path_intern("id.user.banking")
val b = id_path_intern("id.user.banking")
expect a.intern_id to_equal b.intern_id
```

</details>

#### AC-1: returns distinct intern_id for distinct strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = id_path_intern("id.user.banking")
val b = id_path_intern("id.user.mail")
val equal = (a.intern_id == b.intern_id)
expect equal to_equal false
```

</details>

#### AC-1: splits dotted path into ordered segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = id_path_intern("id.user.banking")
expect p.segments to_contain "id"
expect p.segments to_contain "user"
expect p.segments to_contain "banking"
```

</details>

### prefix_match

#### AC-1: grant id.user.banking satisfies required id.user.banking.view

1. expect id path prefix match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = id_path_intern("id.user.banking")
val required = id_path_intern("id.user.banking.view")
expect id_path_prefix_match(grant, required) to_equal true
```

</details>

#### AC-1: grant id.user.mail does NOT satisfy required id.user.banking

1. expect id path prefix match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = id_path_intern("id.user.mail")
val required = id_path_intern("id.user.banking")
expect id_path_prefix_match(grant, required) to_equal false
```

</details>

#### AC-1: sibling prefix does not falsely match

1. expect id path prefix match


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = id_path_intern("id.user.bank")
val required = id_path_intern("id.user.banking")
expect id_path_prefix_match(grant, required) to_equal false
```

</details>

### subdivide

#### AC-1: parent id.user.banking mints child id.user.banking.view

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = id_path_intern("id.user.banking")
val result = id_path_subdivide(parent, "view")
expect result.ok to_equal true
expect result.value.segments to_contain "view"
```

</details>

#### AC-1: cannot mint unrelated id.user.mail from id.user.banking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = id_path_intern("id.user.banking")
val result = id_path_subdivide(parent, "id.user.mail")
expect result.ok to_equal false
```

</details>

### segment validation

#### AC-1: segment containing literal dot is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = id_path_intern("id.user")
val result = id_path_subdivide(parent, "bank.ing")
expect result.ok to_equal false
```

</details>

#### AC-1: empty segment is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent = id_path_intern("id.user")
val result = id_path_subdivide(parent, "")
expect result.ok to_equal false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
