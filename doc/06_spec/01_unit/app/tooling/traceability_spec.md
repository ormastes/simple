# Traceability Checker Specification

> <details>

<!-- sdn-diagram:id=traceability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traceability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traceability_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traceability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traceability Checker Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRC-001 |
| Category | Tooling |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/tooling/traceability_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### traceability helpers

#### normalizes date suffixed slugs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_slug("security_aop_architecture_2026-03-28")).to_equal("security_aop_architecture")
```

</details>

#### extracts relative paths from markdown and plain text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = """
```

</details>

### Math blocks

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
```

</details>

### Math blocks

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
```

</details>

### Math blocks

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
