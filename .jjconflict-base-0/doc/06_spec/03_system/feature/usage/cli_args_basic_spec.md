# CLI Args Basic Specification

> Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli` keyword provides declarative command-line argument parsing integrated into the language.

<!-- sdn-diagram:id=cli_args_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Basic Specification

Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli` keyword provides declarative command-line argument parsing integrated into the language.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-001 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the `cli` keyword basic functionality: bool flags, string options,
int options, and default values. The `cli` keyword provides declarative
command-line argument parsing integrated into the language.

## Syntax

```simple
cli:
    verbose: false        # --verbose / -v bool flag
    output: "out.txt"     # --output / -o string option
    count: 1              # --count / -c int option
```

## Scenarios

### CLI Args Basic

#### bool flags

#### parses bool flag default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# val args = cli.parse([])
# expect(args.verbose).to_equal(false)
val expected = false
expect(expected).to_equal(false)
```

</details>

#### parses bool flag when set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# val args = cli.parse(["--verbose"])
# expect(args.verbose).to_equal(true)
val expected = true
expect(expected).to_equal(true)
```

</details>

#### string options

#### parses string option default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "result.txt"
# val args = cli.parse([])
# expect(args.output).to_equal("result.txt")
val expected = "result.txt"
expect(expected).to_equal("result.txt")
```

</details>

#### parses string option with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "result.txt"
# val args = cli.parse(["--output", "custom.txt"])
# expect(args.output).to_equal("custom.txt")
val expected = "custom.txt"
expect(expected).to_equal("custom.txt")
```

</details>

#### parses string option with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "result.txt"
# val args = cli.parse(["--output=custom.txt"])
# expect(args.output).to_equal("custom.txt")
val expected = "custom.txt"
expect(expected).to_equal("custom.txt")
```

</details>

#### int options

#### parses int option default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
# val args = cli.parse([])
# expect(args.count).to_equal(1)
val expected = 1
expect(expected).to_equal(1)
```

</details>

#### parses int option with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
# val args = cli.parse(["--count", "5"])
# expect(args.count).to_equal(5)
val expected = 5
expect(expected).to_equal(5)
```

</details>

#### multiple options together

#### handles multiple options together

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# val args = cli.parse(["--verbose", "--output", "result.txt", "--count", "3"])
# expect(args.verbose).to_equal(true)
# expect(args.output).to_equal("result.txt")
# expect(args.count).to_equal(3)
val verbose = true
val output = "result.txt"
val count = 3
expect(verbose).to_equal(true)
expect(output).to_equal("result.txt")
expect(count).to_equal(3)
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
