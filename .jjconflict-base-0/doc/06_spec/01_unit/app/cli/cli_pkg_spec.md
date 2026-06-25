# CLI Package Commands Specification

> 1. expect rt file exists str

<!-- sdn-diagram:id=cli_pkg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_pkg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_pkg_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_pkg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Package Commands Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/cli/cli_pkg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CLI Package Commands

#### init app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/init/main.spl")
```

</details>

#### add app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/add/main.spl")
```

</details>

#### remove app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/remove/main.spl")
```

</details>

#### install app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/install/main.spl")
```

</details>

#### update app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/update/main.spl")
```

</details>

#### list app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/list/main.spl")
```

</details>

#### tree app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/tree/main.spl")
```

</details>

#### cache app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/cache/main.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
