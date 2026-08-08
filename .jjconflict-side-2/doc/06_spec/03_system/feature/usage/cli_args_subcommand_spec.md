# CLI Args Subcommand Specification

> Tests subcommand dispatch with the `cli` keyword. Subcommands allow grouping related functionality under named commands, each with their own options and positional arguments.

<!-- sdn-diagram:id=cli_args_subcommand_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_subcommand_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_subcommand_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_subcommand_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# build's --target should not be available under test
# cli.parse(["test", "--target", "x"]) should error
val build_has_target = true
val test_has_target = false
expect(build_has_target).to_equal(true)
expect(test_has_target).to_equal(false)
```

</details>

#### inherits global options in subcommands

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli.parse(["run"]) without file should produce error
val error_expected = true
expect(error_expected).to_equal(true)
```

</details>

#### handles multiple positional args

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val args = cli.parse(["run", "main.spl"])
# expect(args.rest).to_equal([])
val rest = []
expect(rest.len()).to_equal(0)
```

</details>

#### no subcommand given

#### uses default when no subcommand specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
