# Server Specification

> <details>

<!-- sdn-diagram:id=server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Specification

## Scenarios

### Server

#### defines LMS command identity and readiness constants

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/lms/main.spl")

expect(src).to_contain("val SERVER_NAME = \"Simple Language Model Server\"")
expect(src).to_contain("val SERVER_SHORT_NAME = \"Simple LMS\"")
expect(src).to_contain("val SERVER_VERSION = \"0.1.0\"")
expect(src).to_contain("val DEFAULT_PORT = \"8765\"")
expect(src).to_contain("fn main() -> i64:")
expect(src).to_contain("status")
expect(src).to_contain("ready")
```

</details>

#### defines LMS CLI option parsing and help helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/lms/main.spl")

expect(src).to_contain("fn print_help():")
expect(src).to_contain("fn print_help_with_progress(progress_mode: text):")
expect(src).to_contain("fn lms_is_log_option(arg: text) -> bool:")
expect(src).to_contain("fn lms_clean_log_args(args: [text]) -> [text]:")
expect(src).to_contain("fn lms_port_arg(args: [text]) -> text:")
expect(src).to_contain("fn lms_has_unknown_option(args: [text]) -> bool:")
expect(src).to_contain("fn lms_first_unknown_option(args: [text]) -> text:")
expect(src).to_contain("Unknown option:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/lms/server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Server

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
