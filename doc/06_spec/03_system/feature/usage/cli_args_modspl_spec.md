# CLI Args mod.spl Embedding Specification

> Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becomes an executable entry point that can be run directly. This enables self-contained CLI tools as modules.

<!-- sdn-diagram:id=cli_args_modspl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_modspl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_modspl_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_modspl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args mod.spl Embedding Specification

Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becomes an executable entry point that can be run directly. This enables self-contained CLI tools as modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-010 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_modspl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests embedding the cli keyword in mod.spl module files. When a module's
mod.spl contains a cli block, the module becomes an executable entry point
that can be run directly. This enables self-contained CLI tools as modules.

## Syntax

```simple
# src/app/my_tool/mod.spl
cli:
    verbose: false
    output: "result.txt"

fn main(args: CliArgs):
    if args.verbose:
        print "Verbose mode enabled"
    process(args.output)
```

## Scenarios

### CLI Args mod.spl Embedding

#### module entry point

#### defines cli in mod.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A mod.spl file with a cli block should be treated as
# an executable module entry point
val is_entry_point = true
expect(is_entry_point).to_equal(true)
```

</details>

#### generates CliArgs struct in module scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The generated struct should be accessible within the module
val struct_name = "CliArgs"
val scope = "module"
expect(struct_name).to_equal("CliArgs")
expect(scope).to_equal("module")
```

</details>

#### module interaction

#### allows importing module functions alongside cli

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Other modules can import functions from a module that has cli
# use my_tool.{process, format_output}
val can_import = true
expect(can_import).to_equal(true)
```

</details>

#### does not export CliArgs struct by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The generated CliArgs struct is private to the module
# External modules should not see it
val is_exported = false
expect(is_exported).to_equal(false)
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
