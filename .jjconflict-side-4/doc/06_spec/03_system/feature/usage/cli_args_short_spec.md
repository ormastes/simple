# CLI Args Short Names Specification

> Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-character short names from the first letter of the option name, with conflict resolution when multiple options share the same first letter.

<!-- sdn-diagram:id=cli_args_short_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_short_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_short_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_short_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Short Names Specification

Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-character short names from the first letter of the option name, with conflict resolution when multiple options share the same first letter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-003 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_short_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests short name generation and explicit short name overrides for CLI options.
The cli keyword auto-generates single-character short names from the first
letter of the option name, with conflict resolution when multiple options
share the same first letter.

## Syntax

```simple
cli:
    verbose: false                # auto-short: -v
    output: "out.txt"             # auto-short: -o
    count: 1, short: "c"         # explicit short: -c
    color: true, short: "C"      # explicit short: -C (avoids conflict with count)
```

## Scenarios

### CLI Args Short Names

#### auto-generated short names

#### generates short from first letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# cli.parse(["-v"]) should set verbose = true
val short_name = "v"
expect(short_name).to_equal("v")
```

</details>

#### generates short for string option

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "default.txt"
# cli.parse(["-o", "file.txt"]) should set output = "file.txt"
val short_name = "o"
expect(short_name).to_equal("o")
```

</details>

#### generates short for int option

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
# cli.parse(["-c", "5"]) should set count = 5
val short_name = "c"
expect(short_name).to_equal("c")
```

</details>

#### explicit short names

#### uses explicit short name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     threads: 4, short: "t"
# cli.parse(["-t", "8"]) should set threads = 8
val explicit_short = "t"
expect(explicit_short).to_equal("t")
```

</details>

#### allows uppercase short name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     color: true, short: "C"
# cli.parse(["-C"]) should toggle color
val explicit_short = "C"
expect(explicit_short).to_equal("C")
```

</details>

#### conflict resolution

#### skips short when conflict exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
#     color: true
# First option gets -c, second has no auto-short (conflict)
val first_short = "c"
val second_short = ""
expect(first_short).to_equal("c")
expect(second_short).to_equal("")
```

</details>

#### resolves conflict with explicit short

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
#     color: true, short: "C"
# count gets -c, color gets -C (explicit)
val count_short = "c"
val color_short = "C"
expect(count_short).to_equal("c")
expect(color_short).to_equal("C")
```

</details>

#### handles no available short name

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     alpha: false
#     append: true
# alpha gets -a, append gets no short (conflict, no explicit)
val alpha_short = "a"
val append_short = ""
expect(alpha_short).to_equal("a")
expect(append_short).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
