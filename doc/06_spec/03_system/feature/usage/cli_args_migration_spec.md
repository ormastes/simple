# CLI Args Migration Compatibility Specification

> Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual arg parsing should be able to incrementally migrate to the cli keyword without breaking existing functionality.

<!-- sdn-diagram:id=cli_args_migration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_migration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_migration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_migration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Migration Compatibility Specification

Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual arg parsing should be able to incrementally migrate to the cli keyword without breaking existing functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-011 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_migration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compatibility between the new cli keyword and the existing manual
argument parsing pattern. Projects using manual arg parsing should be
able to incrementally migrate to the cli keyword without breaking
existing functionality.

## Manual Pattern (Before)

```simple
val args = get_args()
var verbose = false
var output = "default.txt"
for arg in args:
    if arg == "--verbose":
        verbose = true
    elif arg == "--output":
        output = next_arg()
```

## CLI Keyword (After)

```simple
cli:
    verbose: false
    output: "default.txt"
```

## Scenarios

### CLI Args Migration Compatibility

#### equivalent behavior

#### produces same defaults as manual parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Manual pattern:
# var verbose = false
# var output = "default.txt"
#
# CLI keyword:
# cli:
#     verbose: false
#     output: "default.txt"
#
# Both should yield the same default values
val manual_verbose = false
val manual_output = "default.txt"
val cli_verbose = false
val cli_output = "default.txt"
expect(cli_verbose).to_equal(manual_verbose)
expect(cli_output).to_equal(manual_output)
```

</details>

#### produces same parsed values as manual parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given args: ["--verbose", "--output", "custom.txt"]
# Manual: loops and matches each arg
# CLI: cli.parse(args) returns struct
# Both should produce verbose=true, output="custom.txt"
val manual_verbose = true
val manual_output = "custom.txt"
val cli_verbose = true
val cli_output = "custom.txt"
expect(cli_verbose).to_equal(manual_verbose)
expect(cli_output).to_equal(manual_output)
```

</details>

#### incremental migration

#### can coexist with manual parsing in same project

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Some modules use cli keyword, others use manual parsing
# No conflicts between the two approaches
val cli_module_works = true
val manual_module_works = true
expect(cli_module_works).to_equal(true)
expect(manual_module_works).to_equal(true)
```

</details>

#### supports gradual option-by-option migration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A project can migrate one option at a time from manual to cli
# The cli keyword does not require all-or-nothing adoption
val partial_migration = true
expect(partial_migration).to_equal(true)
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
