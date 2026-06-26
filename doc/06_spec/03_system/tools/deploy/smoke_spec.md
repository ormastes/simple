# Smoke Specification

> <details>

<!-- sdn-diagram:id=smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Specification

## Scenarios

### deploy: binary existence

#### a usable Simple runtime exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = find_simple_binary() != ""
expect(found).to_equal(true)
```

</details>

### deploy: key files present

#### src/ directory exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = file_exists("src")
expect(found).to_equal(true)
```

</details>

#### test/ directory exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = file_exists("test")
expect(found).to_equal(true)
```

</details>

#### CLAUDE.md exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = file_exists("CLAUDE.md")
expect(found).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/deploy/smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- deploy: binary existence
- deploy: key files present

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
