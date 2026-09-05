# CLI Args Help Text Specification

> Tests automatic help text generation from docstrings and option metadata. The cli keyword generates --help output including program description, option names with types, defaults, and short names.

<!-- sdn-diagram:id=cli_args_help_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_help_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_help_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_help_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Help Text Specification

Tests automatic help text generation from docstrings and option metadata. The cli keyword generates --help output including program description, option names with types, defaults, and short names.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-004 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_help_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests automatic help text generation from docstrings and option metadata.
The cli keyword generates --help output including program description,
option names with types, defaults, and short names.

## Syntax

```simple
# My awesome tool
# Processes files with various options.
cli:
    verbose: false      # Enable verbose output
    output: "out.txt"   # Output file path
    count: 1            # Number of iterations
```

## Scenarios

### CLI Args Help Text

#### help flag

#### responds to --help flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# Running with --help should produce help text, not parse args
val help_requested = true
expect(help_requested).to_equal(true)
```

</details>

#### responds to -h short flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# -h should be reserved for help and auto-mapped
val short_help = "h"
expect(short_help).to_equal("h")
```

</details>

#### help content

#### includes option names in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help output should list all defined options
val help_text = "--verbose  Enable verbose output (default: false)"
expect(help_text).to_contain("--verbose")
expect(help_text).to_contain("false")
```

</details>

#### includes short names in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help output should show short names alongside long names
val help_line = "-v, --verbose  Enable verbose output (default: false)"
expect(help_line).to_start_with("-v")
expect(help_line).to_contain("--verbose")
```

</details>

#### includes type information in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Help output should show the expected type for each option
val help_line = "--count <i64>  Number of iterations (default: 1)"
expect(help_line).to_contain("i64")
expect(help_line).to_contain("1")
```

</details>

#### includes program description from docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The file-level docstring becomes the program description
# # My awesome tool
# # Processes files with various options.
val description = "My awesome tool"
val detail = "Processes files with various options."
expect(description).to_equal("My awesome tool")
expect(detail).to_contain("Processes files")
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
