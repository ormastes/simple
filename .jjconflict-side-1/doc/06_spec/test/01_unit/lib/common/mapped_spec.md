# Mapped Specification

> <details>

<!-- sdn-diagram:id=mapped_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mapped_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mapped_spec -> std
mapped_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mapped_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mapped Specification

## Scenarios

### Mapped Types

#### exports and formats mapped-type helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(partial("User")).to_equal("Partial<User>")
expect(readonly_type("Config")).to_equal("Readonly<Config>")
expect(pick_type("User", "name,age")).to_equal("Pick<User, name,age>")
expect(omit_type("User", "password")).to_equal("Omit<User, password>")
```

</details>

#### exports field helper shorthands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(make_optional_field("age")).to_equal("age?")
expect(make_required_field("email")).to_equal("email!")
```

</details>

#### formats mapped result display names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mapped_result_get_type("User", "Partial")).to_equal("Partial<User>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/mapped_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mapped Types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
