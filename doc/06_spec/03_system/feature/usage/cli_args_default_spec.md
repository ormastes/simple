# CLI Args Default Command Specification

> Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when the user invokes the program without a subcommand name.

<!-- sdn-diagram:id=cli_args_default_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_default_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_default_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_default_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Default Command Specification

Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when the user invokes the program without a subcommand name.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-006 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_default_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests default command behavior when no subcommand is specified.
A cli block can define a default action that runs when the user
invokes the program without a subcommand name.

## Syntax

```simple
cli:
    verbose: false

    default:
        # This block runs when no subcommand is given
        positional file: text

    command build:
        target: "debug"
```

## Scenarios

### CLI Args Default Command

#### default block

#### uses default block when no subcommand given

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     default:
#         positional file: text
# val args = cli.parse(["main.spl"])
# expect(args.file).to_equal("main.spl")
val file = "main.spl"
expect(file).to_equal("main.spl")
```

</details>

#### prefers subcommand over default when given

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     default:
#         positional file: text
#     command build:
#         target: "debug"
# val args = cli.parse(["build", "--target", "release"])
# expect(args.command).to_equal("build")
val command = "build"
expect(command).to_equal("build")
```

</details>

#### no default block

#### shows help when no subcommand and no default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command build:
#         target: "debug"
# Running with no args and no default block should show help
val shows_help = true
expect(shows_help).to_equal(true)
```

</details>

#### accepts global options without subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
#     command build:
#         target: "debug"
# val args = cli.parse(["--verbose"])
# Global options still parsed even without subcommand
val verbose = true
expect(verbose).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
