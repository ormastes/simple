# CLI Migration Commands Specification

> 1. expect rt file exists str

<!-- sdn-diagram:id=cli_migration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_migration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_migration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_migration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Migration Commands Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/cli/cli_migration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CLI Migration Commands

#### i18n app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/i18n/main.spl")
```

</details>

#### migrate app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/migrate/main.spl")
```

</details>

#### lock app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/lock/main.spl")
```

</details>

#### qualify_ignore app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/qualify_ignore/main.spl")
```

</details>

#### diagram app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/diagram/main.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
