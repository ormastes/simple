# Feature: Declarative CLI Argument Parsing (`cli` keyword)

**Status:** Proposed
**Date:** 2026-03-03
**Category:** Language Feature
**Priority:** HIGH

---

## Overview

The `cli` keyword provides declarative command-line argument parsing as a first-class language construct. Instead of imperative builder chains (`cli_spec().flag(...).option(...)`), applications define a `cli` block that declares options as struct-like fields with defaults. The compiler generates the argument parser, help text, and type-safe access automatically.

This replaces the current imperative pattern in `src/lib/nogc_sync_mut/cli/cli_parser.spl` and `src/app/cli/` with a concise, declarative syntax inspired by Python's `argparse` and Rust's `clap` derive macros.

## Syntax

```simple
cli Args:
    """My application description."""

    # Bool flags — default false, toggled by --flag-name
    verbose = false
    dry_run = false

    # String options — default is the assigned value
    backend = "auto"
    output = ""

    # Int options — inferred from literal type
    timeout = 0
    jobs = 4

    # Explicit short name with -X prefix
    -g gc_log = false

    # Subcommands
    sub test:
        """Run the test suite."""
        filter = ""
        only_slow = false

    sub build:
        """Build the project."""
        release = false
        target = ""

    # Pass-through subcommands (forward remaining args)
    sub lint, fmt

    # Default action when no subcommand given
    default: .repl

    # File detection by extension
    file: ".spl"
```

**Access pattern:**

```simple
fn main():
    val args = Args.parse()

    if args.verbose:
        print "Verbose mode enabled"

    match args.command:
        case "test":
            run_tests(args.test.filter, args.test.only_slow)
        case "build":
            run_build(args.build.release, args.build.target)
        case nil:
            # default action (.repl) already dispatched
            pass_dn
```

---

## Scenarios

### #CLI-001: Basic bool flag

**Given** a `cli` block with `verbose = false`
**When** the program is invoked with no arguments
**Then** `Args.verbose` is `false`

**When** the program is invoked with `--verbose`
**Then** `Args.verbose` is `true`

```simple
cli Args:
    verbose = false

fn main():
    val args = Args.parse()
    expect(args.verbose).to_equal(false)   # no flag
    # With --verbose: args.verbose == true
```

---

### #CLI-002: String option

**Given** a `cli` block with `backend = "auto"`
**When** the program is invoked with no arguments
**Then** `Args.backend` is `"auto"`

**When** the program is invoked with `--backend=llvm`
**Then** `Args.backend` is `"llvm"`

```simple
cli Args:
    backend = "auto"

fn main():
    val args = Args.parse()
    # Default: args.backend == "auto"
    # --backend=llvm: args.backend == "llvm"
```

---

### #CLI-003: Int option

**Given** a `cli` block with `timeout = 0`
**When** the program is invoked with no arguments
**Then** `Args.timeout` is `0`

**When** the program is invoked with `--timeout=30`
**Then** `Args.timeout` is `30`

```simple
cli Args:
    timeout = 0

fn main():
    val args = Args.parse()
    # Default: args.timeout == 0
    # --timeout=30: args.timeout == 30
```

---

### #CLI-004: Explicit short name

**Given** a `cli` block with `-g gc_log = false`
**When** the program is invoked with `-g`
**Then** `Args.gc_log` is `true`

**When** the program is invoked with `--gc-log`
**Then** `Args.gc_log` is `true` (underscores map to hyphens on the command line)

```simple
cli Args:
    -g gc_log = false

fn main():
    val args = Args.parse()
    # -g: args.gc_log == true
    # --gc-log: args.gc_log == true
```

---

### #CLI-005: Auto short name

**Given** a `cli` block with fields `verbose`, `backend`, `timeout`
**When** no explicit short names are declared
**Then** the compiler auto-generates `-v`, `-b`, `-t` as short names (first letter of each field)

**When** two fields start with the same letter (e.g., `verbose` and `version`)
**Then** the first field gets the short name (`-v` for `verbose`), the second gets none (no `-v` for `version`)

```simple
cli Args:
    verbose = false    # auto: -v
    backend = "auto"   # auto: -b
    timeout = 0        # auto: -t
    version = false    # conflict: no short (verbose already claimed -v)
```

---

### #CLI-006: Help generation

**Given** a `cli` block with a docstring and multiple fields
**When** the program is invoked with `--help` or `-h`
**Then** help text is printed to stdout containing:
  - The docstring as program description
  - Each field with its long name, short name, type, and default value
  - Subcommand list with their docstrings

```simple
cli Args:
    """My compiler tool."""
    verbose = false
    backend = "auto"

    sub build:
        """Build the project."""
        release = false

# --help output:
# My compiler tool.
#
# Usage: program [options] [command]
#
# Options:
#   -v, --verbose          (default: false)
#   -b, --backend=VALUE    (default: auto)
#   -h, --help             Show this help message
#
# Commands:
#   build    Build the project.
```

---

### #CLI-007: Subcommand dispatch

**Given** a `cli` block with `sub test:` containing `filter = ""` and `only_slow = false`
**When** the program is invoked with `test --filter=parser --only-slow`
**Then** `args.command` is `"test"`, `args.test.filter` is `"parser"`, `args.test.only_slow` is `true`

**When** the program is invoked with `test` alone
**Then** `args.command` is `"test"`, `args.test.filter` is `""`, `args.test.only_slow` is `false`

```simple
cli Args:
    sub test:
        """Run the test suite."""
        filter = ""
        only_slow = false

fn main():
    val args = Args.parse()
    if args.command == "test":
        run_tests(args.test.filter, args.test.only_slow)
```

---

### #CLI-008: Default command

**Given** a `cli` block with `default: .repl`
**When** the program is invoked with no subcommand and no file argument
**Then** the method `.repl` is dispatched as the default action
**And** `args.command` is `nil`

```simple
cli Args:
    """Simple language runtime."""

    sub build:
        """Build the project."""
        release = false

    default: .repl

fn repl():
    print "Starting REPL..."

fn main():
    val args = Args.parse()
    match args.command:
        case "build": build(args.build.release)
        case nil: repl()   # default action
```

---

### #CLI-009: File detection

**Given** a `cli` block with `file: ".spl"`
**When** the program is invoked with `program hello.spl`
**Then** `args.file` is `"hello.spl"` (detected by extension match)

**When** the program is invoked with `program build`
**Then** `args.file` is `nil` (no `.spl` extension, treated as subcommand)

**When** the program is invoked with `program src/main.spl --verbose`
**Then** `args.file` is `"src/main.spl"` and `args.verbose` is `true`

```simple
cli Args:
    """Simple language runtime."""
    verbose = false

    sub build:
        """Build the project."""
        release = false

    file: ".spl"

fn main():
    val args = Args.parse()
    if val f = args.file:
        run_file(f)
    else:
        match args.command:
            case "build": build(args.build.release)
            case nil: repl()
```

---

### #CLI-010: Pass-through subcommand

**Given** a `cli` block with `sub lint, fmt`
**When** the program is invoked with `lint --fix --quiet`
**Then** `args.command` is `"lint"` and `args.remaining` is `["--fix", "--quiet"]`

**When** the program is invoked with `fmt src/main.spl`
**Then** `args.command` is `"fmt"` and `args.remaining` is `["src/main.spl"]`

```simple
cli Args:
    verbose = false

    sub test:
        """Run tests."""
        filter = ""

    # Pass-through: remaining args forwarded as-is
    sub lint, fmt

fn main():
    val args = Args.parse()
    match args.command:
        case "lint": run_lint(args.remaining)
        case "fmt": run_fmt(args.remaining)
        case "test": run_tests(args.test.filter)
```

---

## Acceptance Criteria

| ID | Scenario | Criterion | Expected |
|----|----------|-----------|----------|
| AC-01 | #CLI-001 | Bool flag defaults to `false` | `Args.parse()` with no args yields `verbose == false` |
| AC-02 | #CLI-001 | `--verbose` sets flag to `true` | `Args.parse()` with `["--verbose"]` yields `verbose == true` |
| AC-03 | #CLI-002 | String option has default | `Args.parse()` with no args yields `backend == "auto"` |
| AC-04 | #CLI-002 | `--backend=llvm` overrides default | `Args.parse()` with `["--backend=llvm"]` yields `backend == "llvm"` |
| AC-05 | #CLI-003 | Int option has default | `Args.parse()` with no args yields `timeout == 0` |
| AC-06 | #CLI-003 | `--timeout=30` overrides default | `Args.parse()` with `["--timeout=30"]` yields `timeout == 30` |
| AC-07 | #CLI-004 | Explicit short name `-g` maps to field | `Args.parse()` with `["-g"]` yields `gc_log == true` |
| AC-08 | #CLI-004 | Underscores convert to hyphens | `--gc-log` is accepted for field `gc_log` |
| AC-09 | #CLI-005 | Auto short names from first letter | `-v` maps to `verbose`, `-b` maps to `backend` |
| AC-10 | #CLI-005 | Conflicting short names are skipped | Second field starting with same letter gets no short name |
| AC-11 | #CLI-006 | `--help` prints usage and exits | Help text contains program description, all options, and subcommands |
| AC-12 | #CLI-006 | `-h` is alias for `--help` | `-h` produces identical output to `--help` |
| AC-13 | #CLI-007 | Subcommand parsed with own options | `test --filter=parser` yields `command == "test"`, `test.filter == "parser"` |
| AC-14 | #CLI-007 | Subcommand options use defaults | `test` alone yields `test.filter == ""`, `test.only_slow == false` |
| AC-15 | #CLI-008 | Default action when no subcommand | No subcommand yields `command == nil`, default method dispatched |
| AC-16 | #CLI-009 | File argument detected by extension | `hello.spl` yields `file == "hello.spl"` |
| AC-17 | #CLI-009 | Non-matching arg not treated as file | `build` (no `.spl`) treated as subcommand, `file == nil` |
| AC-18 | #CLI-010 | Pass-through forwards remaining args | `lint --fix --quiet` yields `command == "lint"`, `remaining == ["--fix", "--quiet"]` |

---

## Design Decisions

### Why a keyword instead of a library?

The imperative builder pattern (`cli_spec().flag(...).option(...)`) works but has drawbacks:
1. **Boilerplate** -- every option requires a builder call plus a typed accessor call
2. **No static typing** -- option names are strings, typos are runtime errors
3. **No compiler integration** -- help text is manually maintained

The `cli` keyword lets the compiler:
- Infer types from default values (`false` = bool, `"auto"` = text, `0` = i64)
- Generate typed struct fields (compile-time access, no string lookups)
- Auto-generate help text from docstrings and field metadata
- Validate subcommand names at parse time

### Underscore-to-hyphen mapping

Field names use underscores (`gc_log`) but command-line flags use hyphens (`--gc-log`). This follows the convention of Rust's `clap`, Python's `argparse`, and Go's `cobra`. The mapping is automatic and bidirectional.

### Subcommand model

Subcommands with bodies (`sub test:`) define their own option namespace. Pass-through subcommands (`sub lint, fmt`) forward all remaining arguments without parsing. This matches the pattern used in the current `src/app/cli/main.spl` dispatcher.

---

## Related Files

| File | Role |
|------|------|
| `src/lib/nogc_sync_mut/cli/cli_parser.spl` | Current imperative CLI parser (to be replaced for `cli` keyword users) |
| `src/app/cli/main.spl` | Current compiler CLI entry point (manual dispatch) |
| `src/app/cli/dispatch.spl` | Current subcommand dispatch logic |
| `src/compiler_rust/lib/std/examples/cli_demo.spl` | Example using imperative `cli.ArgParser` |
| `src/compiler_rust/lib/std/examples/cli_auto_stage_demo.spl` | Example with file staging |

## References

- Python `argparse`: declarative argument definitions
- Rust `clap` derive: struct-based CLI definition with `#[derive(Parser)]`
- Go `cobra`: subcommand trees with per-command flag sets
- Swift `ArgumentParser`: property-wrapper-based CLI parsing
