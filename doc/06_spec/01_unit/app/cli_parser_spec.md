# Cli Parser Specification

> <details>

<!-- sdn-diagram:id=cli_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Parser Specification

## Scenarios

### CliParser

#### keeps global flag parsing available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = cli_source("main_part1.spl")

expect(source).to_contain("struct GlobalFlags:")
expect(source).to_contain("fn parse_global_flags(args: [text]) -> GlobalFlags")
expect(source).to_contain("gc_log")
expect(source).to_contain("gc_off")
expect(source).to_contain("run_config")
expect(source).to_contain("jit_threshold")
expect(source).to_contain("stack_overflow_detection")
```

</details>

#### keeps command dispatch table entry points available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = cli_source("dispatch.spl")

expect(source).to_contain("fn find_command(cmd: text) -> CommandEntry?")
expect(source).to_contain("fn dispatch_command(entry: CommandEntry, args: [text], gc_log: bool, gc_off: bool) -> i64")
expect(source).to_contain("fn try_simple_app(app_path: text, args: [text], gc_log: bool, gc_off: bool) -> i64?")
expect(source).to_contain("fn command_count() -> i64")
expect(source).to_contain("fn coverage_percentage() -> f64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CliParser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
