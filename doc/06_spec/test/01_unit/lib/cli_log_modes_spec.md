# Cli Log Modes Specification

> <details>

<!-- sdn-diagram:id=cli_log_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_log_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_log_modes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_log_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Log Modes Specification

## Scenarios

### CLI Log Modes

#### uses human stdout summary defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_log_options([])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("human")
expect(opts.surface).to_equal("stdout")
expect(opts.progress).to_equal("summary")
```

</details>

#### parses LLM TUI count options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_log_options(["--log-mode=llm", "--tui", "--progress=count"])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("llm")
expect(opts.surface).to_equal("tui")
expect(opts.progress).to_equal("count")
```

</details>

#### parses shorthand JSON and dot progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_log_options(["--json", "--dots"])
expect(opts.valid).to_equal(true)
expect(opts.log_mode).to_equal("json")
expect(opts.progress).to_equal("dot")
```

</details>

#### quiet disables progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_log_options(["--quiet", "--progress=dot"])
expect(opts.quiet).to_equal(true)
expect(opts.progress).to_equal("dot")
val quiet_last = parse_log_options(["--progress=dot", "--quiet"])
expect(quiet_last.progress).to_equal("none")
```

</details>

#### rejects invalid modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_log_options(["--log-mode=noisy"])
expect(opts.valid).to_equal(false)
expect(opts.error).to_contain("invalid --log-mode")
```

</details>

#### publishes help text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = log_options_help()
expect(lines.len()).to_be_greater_than(0)
expect(lines[0]).to_contain("--log-mode")
```

</details>

#### renders progress modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(render_progress("none", 3, 10, "build")).to_equal("")
expect(render_progress("dot", 3, 10, "build")).to_equal(".")
expect(render_progress("count", 3, 10, "build")).to_equal("3/10 build")
expect(render_progress("summary", 3, 10, "build")).to_equal("build: 3/10 (30%)")
```

</details>

#### renders human TUI grouped counts

1. SimpleProgressGroup new
2. SimpleProgressGroup new


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = [
    SimpleProgressGroup.new("compile", 3, 10, "active"),
    SimpleProgressGroup.new("test", 5, 5, "done")
]
val text = render_tui_grouped_counts("build", groups)
expect(text).to_contain("build")
expect(text).to_contain("groups: 2")
expect(text).to_contain("[active] compile 3/10 (30%)")
expect(text).to_contain("[done] test 5/5 (100%)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_log_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLI Log Modes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
