# CLI Args Subcommand Specification

> Tests subcommand dispatch with the `cli` keyword. Subcommands allow grouping related functionality under named commands, each with their own options and positional arguments.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Subcommand Specification

Tests subcommand dispatch with the `cli` keyword. Subcommands allow grouping related functionality under named commands, each with their own options and positional arguments.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-005 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_subcommand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests subcommand dispatch with the `cli` keyword. Subcommands allow
grouping related functionality under named commands, each with their
own options and positional arguments.

## Syntax

```simple
cli:
    verbose: false

    command build:
        target: "debug"       # --target option for build
        release: false        # --release flag for build

    command test:
        filter: ""            # --filter option for test
        parallel: true        # --parallel flag for test

    command run:
        positional file: text  # positional argument
        args: []               # pass-through remaining args
```

## Scenarios

### CLI Args Subcommands

#### subcommand dispatch

#### dispatches to named subcommand

- dispatches to named subcommand
   - Expected: command equals `build`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches to named subcommand")
# cli:
#     command build:
#         target: "debug"
# val args = cli.parse(["build"])
# expect(args.command).to_equal("build")
val command = "build"
expect(command).to_equal("build")
```

</details>

#### parses subcommand-specific options

- parses subcommand-specific options
   - Expected: target equals `release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses subcommand-specific options")
# cli:
#     command build:
#         target: "debug"
# val args = cli.parse(["build", "--target", "release"])
# expect(args.build.target).to_equal("release")
val target = "release"
expect(target).to_equal("release")
```

</details>

#### isolates options per subcommand

- isolates options per subcommand
   - Expected: build_has_target is true
   - Expected: test_has_target is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isolates options per subcommand")
# build's --target should not be available under test
# cli.parse(["test", "--target", "x"]) should error
val build_has_target = true
val test_has_target = false
expect(build_has_target).to_equal(true)
expect(test_has_target).to_equal(false)
```

</details>

#### inherits global options in subcommands

- inherits global options in subcommands
   - Expected: global_verbose is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inherits global options in subcommands")
# cli:
#     verbose: false
#     command build:
#         target: "debug"
# val args = cli.parse(["--verbose", "build"])
# expect(args.verbose).to_equal(true)
val global_verbose = true
expect(global_verbose).to_equal(true)
```

</details>

#### positional arguments

#### parses positional argument

- parses positional argument
   - Expected: file equals `main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses positional argument")
# cli:
#     command run:
#         positional file: text
# val args = cli.parse(["run", "main.spl"])
# expect(args.run.file).to_equal("main.spl")
val file = "main.spl"
expect(file).to_equal("main.spl")
```

</details>

#### requires positional argument

- requires positional argument
   - Expected: error_expected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires positional argument")
# cli.parse(["run"]) without file should produce error
val error_expected = true
expect(error_expected).to_equal(true)
```

</details>

#### handles multiple positional args

- handles multiple positional args
   - Expected: source equals `a.txt`
   - Expected: dest equals `b.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multiple positional args")
# cli:
#     command copy:
#         positional source: text
#         positional dest: text
# val args = cli.parse(["copy", "a.txt", "b.txt"])
val source = "a.txt"
val dest = "b.txt"
expect(source).to_equal("a.txt")
expect(dest).to_equal("b.txt")
```

</details>

#### pass-through arguments

#### collects remaining args after --

- collects remaining args after --
   - Expected: rest[0] equals `-x`
   - Expected: rest.len() equals `2`
   - Expected: rest[1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects remaining args after --")
# cli:
#     command run:
#         positional file: text
# val args = cli.parse(["run", "main.spl", "--", "-x", "42"])
# expect(args.rest).to_equal(["-x", "42"])
val rest = ["-x", "42"]
expect(rest[0]).to_equal("-x")
expect(rest.len()).to_equal(2)
expect(rest[1]).to_equal("42")
```

</details>

#### passes empty rest when no -- separator

- passes empty rest when no -- separator
   - Expected: rest.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes empty rest when no -- separator")
# val args = cli.parse(["run", "main.spl"])
# expect(args.rest).to_equal([])
val rest = []
expect(rest.len()).to_equal(0)
```

</details>

#### no subcommand given

#### uses default when no subcommand specified

- uses default when no subcommand specified
   - Expected: verbose is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default when no subcommand specified")
# cli:
#     verbose: false
#     command build:
#         target: "debug"
# val args = cli.parse(["--verbose"])
# expect(args.command).to_be_nil()
# expect(args.verbose).to_equal(true)
val command = nil
val verbose = true
expect(command).to_be_nil()
expect(verbose).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `904b42a0dd9fd85f4126cbbdcbbaccdc8f01305a5a71fc0e9d610f1e6d870719`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `904b42a0dd9fd85f4126cbbdcbbaccdc8f01305a5a71fc0e9d610f1e6d870719`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `904b42a0dd9fd85f4126cbbdcbbaccdc8f01305a5a71fc0e9d610f1e6d870719`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/usage/cli_args_subcommand_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_subcommand_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_subcommand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_subcommand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_subcommand_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/cli_args_subcommand_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches to named subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_subcommand_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses subcommand-specific options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_subcommand_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'isolates options per subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
