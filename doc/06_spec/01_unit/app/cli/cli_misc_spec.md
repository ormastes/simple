# CLI Misc Commands Specification

> 1. expect rt file exists str

<!-- sdn-diagram:id=cli_misc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_misc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_misc_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_misc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Misc Commands Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/cli/cli_misc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CLI Misc Commands

#### watch app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/watch/main.spl")
```

</details>

#### web app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/web/main.spl")
```

</details>

#### run app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/run/main.spl")
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
