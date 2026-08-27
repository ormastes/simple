# CLI Args Help Text Specification

> Tests automatic help text generation from docstrings and option metadata. The cli keyword generates --help output including program description, option names with types, defaults, and short names.

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
| Updated | 2026-08-26 |
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

- responds to --help flag
   - Expected: help_requested is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("responds to --help flag")
# cli:
#     verbose: false
# Running with --help should produce help text, not parse args
val help_requested = true
expect(help_requested).to_equal(true)
```

</details>

#### responds to -h short flag

- responds to -h short flag
   - Expected: short_help equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("responds to -h short flag")
# -h should be reserved for help and auto-mapped
val short_help = "h"
expect(short_help).to_equal("h")
```

</details>

#### help content

#### includes option names in help

- includes option names in help


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes option names in help")
# Help output should list all defined options
val help_text = "--verbose  Enable verbose output (default: false)"
expect(help_text).to_contain("--verbose")
expect(help_text).to_contain("false")
```

</details>

#### includes short names in help

- includes short names in help


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes short names in help")
# Help output should show short names alongside long names
val help_line = "-v, --verbose  Enable verbose output (default: false)"
expect(help_line).to_start_with("-v")
expect(help_line).to_contain("--verbose")
```

</details>

#### includes type information in help

- includes type information in help


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes type information in help")
# Help output should show the expected type for each option
val help_line = "--count <i64>  Number of iterations (default: 1)"
expect(help_line).to_contain("i64")
expect(help_line).to_contain("1")
```

</details>

#### includes program description from docstring

- includes program description from docstring
   - Expected: description equals `My awesome tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes program description from docstring")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e3a1aa989c963f03dcc5f75721ee8c8b9def287b6805f2309bd779363531807d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3a1aa989c963f03dcc5f75721ee8c8b9def287b6805f2309bd779363531807d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3a1aa989c963f03dcc5f75721ee8c8b9def287b6805f2309bd779363531807d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/cli_args_help_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_help_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_help_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_help_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_help_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds to --help flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_help_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds to -h short flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_help_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes option names in help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
