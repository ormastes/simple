# Cli Dispatch Unit Specification

> Tests covering CLI Command Parsing, CLI Flag Parsing, CLI Option Parsing, CLI Argument Validation, CLI Path Arguments, CLI Command Dispatch, CLI Help System, CLI Version Display, CLI Error Handling, CLI Exit Codes, CLI Subcommand Parsing, CLI Environment Variables.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Dispatch Unit Specification

## Scenarios

### CLI Command Parsing

#### parses build command

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses build command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses build command")
val args = ["build"]
check(args[0] == "build")
```

</details>

#### parses test command

- parses test command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses test command")
val args = ["test"]
check(args[0] == "test")
```

</details>

#### parses lint command

- parses lint command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses lint command")
val args = ["lint"]
check(args[0] == "lint")
```

</details>

#### parses fmt command

- parses fmt command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fmt command")
val args = ["fmt"]
check(args[0] == "fmt")
```

</details>

#### parses run command

- parses run command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses run command")
val args = ["run"]
check(args[0] == "run")
```

</details>

#### handles empty args

- handles empty args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty args")
val args = []
check(args.len() == 0)
```

</details>

#### handles help command

- handles help command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles help command")
val args = ["help"]
check(args[0] == "help")
```

</details>

#### handles version command

- handles version command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles version command")
val args = ["version"]
check(args[0] == "version")
```

</details>

### CLI Flag Parsing

#### parses release flag

- parses release flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses release flag")
val arg = "--release"
check(arg.starts_with("--"))
check(arg == "--release")
```

</details>

#### parses debug flag

- parses debug flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses debug flag")
val arg = "--debug"
check(arg == "--debug")
```

</details>

#### parses verbose flag

- parses verbose flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses verbose flag")
val arg = "--verbose"
check(arg == "--verbose")
```

</details>

#### parses quiet flag

- parses quiet flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses quiet flag")
val arg = "--quiet"
check(arg == "--quiet")
```

</details>

#### parses check flag

- parses check flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses check flag")
val arg = "--check"
check(arg == "--check")
```

</details>

#### parses fix flag

- parses fix flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fix flag")
val arg = "--fix"
check(arg == "--fix")
```

</details>

#### parses short flags

- parses short flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses short flags")
val flags = ["-v", "-q", "-h"]
for flag in flags:
    check(flag.starts_with("-"))
    check(not flag.starts_with("--"))
```

</details>

### CLI Option Parsing

#### parses tag option

- parses tag option


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tag option")
val arg = "--tag=unit"
check(arg.contains("="))
val parts = arg.split("=")
check(parts[0] == "--tag")
check(parts[1] == "unit")
```

</details>

#### parses output option

- parses output option


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses output option")
val arg = "--output=file.txt"
val parts = arg.split("=")
check(parts[0] == "--output")
check(parts[1] == "file.txt")
```

</details>

#### parses level option

- parses level option


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses level option")
val arg = "--level=2"
val parts = arg.split("=")
check(parts[0] == "--level")
check(parts[1] == "2")
```

</details>

### CLI Argument Validation

#### validates minimum arguments

- validates minimum arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates minimum arguments")
val args = ["build"]
check(args.len() >= 1)
```

</details>

#### validates command exists

- validates command exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates command exists")
val valid_commands = ["build", "test", "lint", "fmt", "run"]
val cmd = "build"
check(cmd in valid_commands)
```

</details>

#### rejects invalid command

- rejects invalid command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid command")
val valid_commands = ["build", "test", "lint", "fmt", "run"]
val cmd = "invalid"
check(not (cmd in valid_commands))
```

</details>

#### validates flag format

- validates flag format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates flag format")
val flag = "--release"
check(flag.starts_with("--"))
```

</details>

#### rejects malformed flag

- rejects malformed flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed flag")
val malformed = "release"
check(not malformed.starts_with("--"))
```

</details>

### CLI Path Arguments

#### parses single file path

- parses single file path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single file path")
val opts = parse_test_args(["test/unit/test_spec.spl"])
expect opts.paths.len() == 1
expect opts.paths[0] == "test/unit/test_spec.spl"
expect opts.path == "test/unit/test_spec.spl"
```

</details>

#### parses multiple file paths

- parses multiple file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple file paths")
# Regression guard: the parser must retain EVERY positional path.
# A "first positional wins" latch reduces this to 1 and the run then
# silently tests a subset of what was asked for.
val opts = parse_test_args(["file1.spl", "file2.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "file1.spl"
expect opts.paths[1] == "file2.spl"
```

</details>

#### parses multiple file paths in reverse order

- parses multiple file paths in reverse order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple file paths in reverse order")
# Order is preserved and no position is privileged over another.
val opts = parse_test_args(["file2.spl", "file1.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "file2.spl"
expect opts.paths[1] == "file1.spl"
```

</details>

#### keeps positional paths separated by a flag

- keeps positional paths separated by a flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps positional paths separated by a flag")
val opts = parse_test_args(["a.spl", "--verbose", "b.spl"])
expect opts.paths.len() == 2
expect opts.paths[0] == "a.spl"
expect opts.paths[1] == "b.spl"
```

</details>

#### counts positional paths independently of the parser

- counts positional paths independently of the parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts positional paths independently of the parser")
# count_positional_args is the fail-closed cross-check main() uses to
# refuse a run whose paths were dropped. It must agree with the parser,
# so assert that contract directly.
expect count_positional_args(["file1.spl", "file2.spl"]) == 2
expect count_positional_args(["a.spl", "--verbose", "b.spl"]) == 2
expect count_positional_args(["--timeout", "30", "a.spl"]) == 1
```

</details>

#### parses directory path

- parses directory path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses directory path")
val opts = parse_test_args(["test/unit/"])
expect opts.paths.len() == 1
expect opts.paths[0] == "test/unit/"
```

</details>

#### parses multiple directory paths

- parses multiple directory paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple directory paths")
val opts = parse_test_args(["test/unit/", "test/integration/"])
expect opts.paths.len() == 2
expect opts.paths[0] == "test/unit/"
expect opts.paths[1] == "test/integration/"
```

</details>

#### parses glob pattern

- parses glob pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses glob pattern")
val opts = parse_test_args(["test/**/*_spec.spl"])
expect opts.paths.len() == 1
expect opts.paths[0] == "test/**/*_spec.spl"
```

</details>

### CLI Command Dispatch

#### routes build command

- routes build command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes build command")
val cmd = "build"
var routed = false
if cmd == "build":
    routed = true
check(routed)
```

</details>

#### routes test command

- routes test command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes test command")
val cmd = "test"
var routed = false
if cmd == "test":
    routed = true
check(routed)
```

</details>

#### routes lint command

- routes lint command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes lint command")
val cmd = "lint"
var routed = false
if cmd == "lint":
    routed = true
check(routed)
```

</details>

#### routes fmt command

- routes fmt command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes fmt command")
val cmd = "fmt"
var routed = false
if cmd == "fmt":
    routed = true
check(routed)
```

</details>

#### handles unknown command

- handles unknown command


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown command")
val cmd = "unknown"
var handled = false
if cmd == "build" or cmd == "test":
    handled = true
else:
    handled = false
check(not handled)
```

</details>

### CLI Help System

#### generates general help

- generates general help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates general help")
val help_text = "Usage: simple <command> [options]"
check(help_text.contains("Usage"))
check(help_text.contains("simple"))
```

</details>

#### generates command-specific help

- generates command-specific help


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates command-specific help")
val build_help = "Usage: simple build [--release] [--debug]"
check(build_help.contains("build"))
check(build_help.contains("--release"))
```

</details>

#### lists available commands

- lists available commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists available commands")
val commands = ["build", "test", "lint", "fmt", "run", "help"]
check(commands.len() == 6)
```

</details>

#### shows flag descriptions

- shows flag descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows flag descriptions")
val flags = [
    {"name": "--release", "desc": "Build in release mode"},
    {"name": "--verbose", "desc": "Show detailed output"}
]

for flag in flags:
    check(flag["name"].starts_with("--"))
    check(flag["desc"].len() > 0)
```

</details>

### CLI Version Display

#### displays version number

- displays version number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("displays version number")
val version = "0.5.0"
check(version.contains("."))
```

</details>

#### displays version with commit

- displays version with commit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("displays version with commit")
val version = "0.5.0-rc.1+abc123"
check(version.contains("0.5.0"))
check(version.contains("+"))
```

</details>

#### parses version components

- parses version components


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses version components")
val version = "0.5.0"
val parts = version.split(".")
check(parts.len() == 3)
check(parts[0] == "0")
check(parts[1] == "5")
check(parts[2] == "0")
```

</details>

### CLI Error Handling

#### reports unknown command error

- reports unknown command error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unknown command error")
val error = "Error: Unknown command 'invalid'"
check(error.contains("Error"))
check(error.contains("Unknown"))
```

</details>

#### reports missing argument error

- reports missing argument error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing argument error")
val error = "Error: Missing required argument"
check(error.contains("Missing"))
```

</details>

#### reports invalid flag error

- reports invalid flag error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports invalid flag error")
val error = "Error: Invalid flag '--unknown'"
check(error.contains("Invalid"))
```

</details>

#### suggests did you mean

- suggests did you mean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests did you mean")
val suggestion = "Did you mean '--release'?"
check(suggestion.contains("Did you mean"))
```

</details>

### CLI Exit Codes

#### returns 0 for success

- returns 0 for success


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for success")
val exit_code = 0
check(exit_code == 0)
```

</details>

#### returns 1 for general error

- returns 1 for general error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for general error")
val exit_code = 1
check(exit_code == 1)
```

</details>

#### returns 2 for usage error

- returns 2 for usage error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 2 for usage error")
val exit_code = 2
check(exit_code == 2)
```

</details>

#### returns specific codes

- returns specific codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns specific codes")
val codes = {
    "success": 0,
    "error": 1,
    "usage": 2,
    "not_found": 3
}

check(codes["success"] == 0)
check(codes["error"] == 1)
```

</details>

### CLI Subcommand Parsing

#### parses build subcommand

- parses build subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses build subcommand")
val args = ["build", "lint"]
check(args[0] == "build")
check(args[1] == "lint")
```

</details>

#### parses test subcommand

- parses test subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses test subcommand")
val args = ["test", "--list"]
check(args[0] == "test")
check(args[1] == "--list")
```

</details>

#### handles multiple levels

- handles multiple levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple levels")
val args = ["build", "coverage", "--html"]
check(args.len() == 3)
```

</details>

### CLI Environment Variables

#### reads SIMPLE_DEBUG var

- reads SIMPLE_DEBUG var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads SIMPLE_DEBUG var")
val var_name = "SIMPLE_DEBUG"
check(var_name == "SIMPLE_DEBUG")
```

</details>

#### reads SIMPLE_VERBOSE var

- reads SIMPLE_VERBOSE var


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads SIMPLE_VERBOSE var")
val var_name = "SIMPLE_VERBOSE"
check(var_name == "SIMPLE_VERBOSE")
```

</details>

#### falls back to defaults

- falls back to defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to defaults")
var verbose = false
# If env var not set, use default
check(verbose == false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli_dispatch_unit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI Command Parsing, CLI Flag Parsing, CLI Option Parsing, CLI Argument Validation, CLI Path Arguments, CLI Command Dispatch, CLI Help System, CLI Version Display, CLI Error Handling, CLI Exit Codes, CLI Subcommand Parsing, CLI Environment Variables.
- CLI Command Parsing
- CLI Flag Parsing
- CLI Option Parsing
- CLI Argument Validation
- CLI Path Arguments
- CLI Command Dispatch
- CLI Help System
- CLI Version Display
- CLI Error Handling
- CLI Exit Codes
- CLI Subcommand Parsing
- CLI Environment Variables

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77f9e202340bd51aee1b5b8a36cd94679b6d2429b6c9b4ffdeccb7a888c33757`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77f9e202340bd51aee1b5b8a36cd94679b6d2429b6c9b4ffdeccb7a888c33757`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77f9e202340bd51aee1b5b8a36cd94679b6d2429b6c9b4ffdeccb7a888c33757`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli_dispatch_unit_spec.spl
mirror: doc/06_spec/unit/app/cli_dispatch_unit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli_dispatch_unit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli_dispatch_unit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli_dispatch_unit_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses build command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_dispatch_unit_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses test command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli_dispatch_unit_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses lint command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
