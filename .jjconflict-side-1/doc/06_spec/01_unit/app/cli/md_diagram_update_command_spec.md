# Md Diagram Update Command Specification

> <details>

<!-- sdn-diagram:id=md_diagram_update_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_diagram_update_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_diagram_update_command_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_diagram_update_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Diagram Update Command Specification

## Scenarios

### CLI md-diagram-update command

#### is registered in the Simple dispatch sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val main_source = rt_file_read_text("src/app/cli/main_part2.spl") ?? ""
val table_source = rt_file_read_text("src/app/cli/dispatch/table.spl") ?? ""
expect(main_source).to_contain("str_eq(first, \"md-diagram-update\")")
expect(main_source).to_contain("src/app/md_diagram_update/main.spl")
expect(table_source).to_contain("name: \"md-diagram-update\"")
expect(table_source).to_contain("app_path: \"src/app/md_diagram_update/main.spl\"")
```

</details>

#### is registered in the Rust bootstrap driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/compiler_rust/driver/src/main.rs") ?? ""
expect(source).to_contain("name: \"md-diagram-update\"")
expect(source).to_contain("app_path: \"src/app/md_diagram_update/main.spl\"")
```

</details>

#### is visible in CLI help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rust_help = rt_file_read_text("src/compiler_rust/driver/src/cli/help.rs") ?? ""
val simple_help = rt_file_read_text("src/app/cli/cli_helpers.spl") ?? ""
expect(rust_help).to_contain("simple md-diagram-update [file.md ...]")
expect(simple_help).to_contain("simple md-diagram-update [file.md ...]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/md_diagram_update_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLI md-diagram-update command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
