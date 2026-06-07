# Principal Specification

> Principal kind validation — local principal default; non-local rejected.

<!-- sdn-diagram:id=principal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=principal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

principal_spec -> std
principal_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=principal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Principal Specification

Principal kind validation — local principal default; non-local rejected.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/principal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Principal kind validation — local principal default; non-local rejected.

## Scenarios

### Principal

### kinds

#### AC-1: default principal is Local

1. expect principal is local


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Principal.default_local("alice")
expect principal_is_local(p) to_equal true
```

</details>

#### AC-1: local principal passes validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Principal(kind: PrincipalKind.Local, id: "alice")
val result = principal_validate(p)
expect result.ok to_equal true
```

</details>

#### AC-1: non-local principal is rejected in this release

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Principal(kind: PrincipalKind.Remote, id: "host:alice")
val result = principal_validate(p)
expect result.ok to_equal false
```

</details>

#### AC-1: non-local principal_is_local returns false

1. expect principal is local


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Principal(kind: PrincipalKind.Remote, id: "host:alice")
expect principal_is_local(p) to_equal false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
