# CLI Codegen Commands Specification

> 1. expect rt file exists str

<!-- sdn-diagram:id=cli_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_codegen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Codegen Commands Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/cli/cli_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CLI Codegen Commands

#### gen_lean app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/gen_lean/main.spl")
```

</details>

#### feature_gen app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/feature_gen/main.spl")
```

</details>

#### task_gen app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/task_gen/main.spl")
```

</details>

#### spec_gen app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/spec_gen/main.spl")
```

</details>

#### todo_scan app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/todo_scan/main.spl")
```

</details>

#### todo_gen app

#### has Simple app wrapper

1. expect rt file exists str


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_file_exists_str("src/app/todo_gen/main.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
