# Main Opt Level Cli Specification

> <details>

<!-- sdn-diagram:id=main_opt_level_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_opt_level_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_opt_level_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_opt_level_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Opt Level Cli Specification

## Scenarios

### standalone driver opt-level parsing

#### accepts inline legacy numeric opt levels 0 through 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["0", "1", "2", "3"]
for level in levels:
    val result = run_standalone_driver("simple-compiler --opt-level=" + level + " missing_input.spl")
    expect(result.0.contains("Invalid optimization level")).to_equal(false)
    expect(result.0.contains("Optimization level must be 0-3")).to_equal(false)
```

</details>

#### accepts split legacy numeric opt levels 0 through 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val levels = ["0", "1", "2", "3"]
for level in levels:
    val result = run_standalone_driver("simple-compiler --opt-level " + level + " missing_input.spl")
    expect(result.0.contains("Invalid optimization level")).to_equal(false)
    expect(result.0.contains("Optimization level must be 0-3")).to_equal(false)
```

</details>

#### rejects out-of-range legacy numeric opt levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_standalone_driver("simple-compiler --opt-level=4 missing_input.spl")
expect(result.2).to_equal(1)
expect(result.0).to_contain("Optimization level must be 0-3")
```

</details>

#### rejects non-numeric legacy opt levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_standalone_driver("simple-compiler --opt-level=basic missing_input.spl")
expect(result.2).to_equal(1)
expect(result.0).to_contain("Invalid optimization level: basic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/main_opt_level_cli_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- standalone driver opt-level parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
