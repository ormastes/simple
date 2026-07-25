# Shell Tools Slice Specification

> _Regression checks for shell ls/find argument handling._

<!-- sdn-diagram:id=shell_tools_slice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_tools_slice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_tools_slice_spec -> std
shell_tools_slice_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_tools_slice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Tools Slice Specification

## Scenarios

### shell_tools_slice feature spec
_Regression checks for shell ls/find argument handling._

#### parses ls help, path, and unknown options

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = parse_ls_args("/home", ["--help"])
expect(help.is_ok()).to_equal(true)
expect(help.unwrap().help_requested).to_equal(true)

val parsed = parse_ls_args("/home", ["-a", "docs"])
expect(parsed.is_ok()).to_equal(true)
expect(parsed.unwrap().path).to_equal("/home/docs")
expect(parsed.unwrap().show_all).to_equal(true)
expect(format_ls_usage()).to_contain("ls [-a] [-l] [PATH]")

val unknown = parse_ls_args("/home", ["-z"])
expect(unknown.is_err()).to_equal(true)
```

</details>

#### parses find forms and matches glob-style patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val by_name = parse_find_args("/work", ["-name", "*.spl"])
expect(by_name.is_ok()).to_equal(true)
expect(by_name.unwrap().start_path).to_equal("/work")
expect(by_name.unwrap().name_pattern).to_equal("*.spl")

val with_path = parse_find_args("/work", ["src", "-name", "find?.spl"])
expect(with_path.is_ok()).to_equal(true)
expect(with_path.unwrap().start_path).to_equal("/work/src")
expect(with_path.unwrap().name_pattern).to_equal("find?.spl")

expect(find_name_matches("*.spl", "find_tool.spl")).to_equal(true)
expect(find_name_matches("find?.spl", "find1.spl")).to_equal(true)
expect(find_name_matches("find?.spl", "find_tool.spl")).to_equal(false)
expect(format_find_usage()).to_contain("find [PATH] [-name PATTERN]")
```

</details>

#### rejects malformed find arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_find_args("/work", ["-name"]).is_err()).to_equal(true)
expect(parse_find_args("/work", ["-x"]).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/shell_tools_slice_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shell_tools_slice feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
