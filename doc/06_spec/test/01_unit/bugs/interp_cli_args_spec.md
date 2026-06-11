# Interp Cli Args Specification

> <details>

<!-- sdn-diagram:id=interp_cli_args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interp_cli_args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interp_cli_args_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interp_cli_args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Cli Args Specification

## Scenarios

### rt_cli_get_args() runtime args bug

#### demonstrates the stripping workaround

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the array directly (var: [text] = [] broken in it blocks)
val simulated_raw = ["simple", "run", "test/example.spl", "--flag", "value"]
val user_args = strip_runtime_args(simulated_raw)
expect(_len(user_args)).to_equal(2)
expect(_get(user_args, 0)).to_equal("--flag")
expect(_get(user_args, 1)).to_equal("value")
```

</details>

#### handles no script path gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_script = ["--something"]
val result = strip_runtime_args(no_script)
expect(result.len()).to_equal(0)
```

</details>

#### handles empty args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = _empty_text_list()
val result = strip_runtime_args(empty)
expect(result.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/interp_cli_args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rt_cli_get_args() runtime args bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
