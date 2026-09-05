# Cli Args Mutability Specification

> <details>

<!-- sdn-diagram:id=cli_args_mutability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_mutability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_mutability_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_mutability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Args Mutability Specification

## Scenarios

### compiler driver CLI args mutability

#### marks mutating legacy opt-level helper as me

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/80.driver/main.spl")

expect(source).to_contain("me apply_legacy_opt_level(level: i64):")
expect(source).to_contain("me parse_long_option(arg: text, mut result: CliArgs)")
expect(source).to_contain("fn apply_option(name: text, value: text, mut result: CliArgs)")
expect(source).to_contain("me parse_short_option(arg: text, mut result: CliArgs)")
expect(source.contains("fn apply_legacy_opt_level(level: i64):")).to_equal(false)
expect(source.contains("val arg = if val next_arg = self.next()")).to_equal(false)
expect(source.contains("val file = if val next_file = self.next()")).to_equal(false)
expect(source.contains("= if val")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/cli_args_mutability_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compiler driver CLI args mutability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
