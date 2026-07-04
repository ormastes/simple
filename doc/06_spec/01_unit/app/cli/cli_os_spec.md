# Cli Os Specification

> <details>

<!-- sdn-diagram:id=cli_os_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_os_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_os_spec -> std
cli_os_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_os_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Os Specification

## Scenarios

### Top-level SimpleOS CLI wrapper

#### dispatches os targets successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["targets"])).to_equal(0)
```

</details>

#### accepts os help aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["help"])).to_equal(0)
expect(handle_os_inline(["--help"])).to_equal(0)
```

</details>

#### rejects unknown os subcommands with a non-zero exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["unknown-subcommand"])).to_equal(1)
```

</details>

#### keeps the last valid --log occurrence across mixed forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prior = env_get("SIMPLE_OS_LOG_MODE")
val before = if prior == nil: "" else: prior
expect(handle_os_inline(["build", "--log=off", "--log", "on", "--arch=bogus"])).to_equal(1)
expect(env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(before)
```

</details>

#### rejects bare --arch followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["build", "--arch", "--log=off"])).to_equal(1)
```

</details>

#### rejects bare --target followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["build", "--target", "--log=off"])).to_equal(1)
```

</details>

#### rejects bare --scenario followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os_inline(["build", "--scenario", "--arch=x86_64"])).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/cli_os_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Top-level SimpleOS CLI wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
