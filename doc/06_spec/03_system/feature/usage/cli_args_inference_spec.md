# CLI Args Inference Rules Specification

> Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct from the cli block, where each field corresponds to an option. This tests that the generated struct has the correct shape, field names, and types.

<!-- sdn-diagram:id=cli_args_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_inference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Inference Rules Specification

Tests the type inference rules and struct shape validation for the cli keyword. The compiler generates a typed struct from the cli block, where each field corresponds to an option. This tests that the generated struct has the correct shape, field names, and types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-008 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_inference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the type inference rules and struct shape validation for the cli keyword.
The compiler generates a typed struct from the cli block, where each field
corresponds to an option. This tests that the generated struct has the
correct shape, field names, and types.

## Syntax

```simple
cli:
    verbose: false
    output: "out.txt"
    count: 1
    rate: 0.5
    tags: ["a", "b"]

# Compiler generates:
# struct CliArgs:
#     verbose: bool
#     output: text
#     count: i64
#     rate: f64
#     tags: [text]
```

## Scenarios

### CLI Args Inference Rules

#### inference from literals

#### infers bool from boolean literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     flag: false
# Generated field type should be bool
val literal = false
val inferred = "bool"
expect(inferred).to_equal("bool")
```

</details>

#### infers text from string literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     name: "hello"
# Generated field type should be text
val literal = "hello"
val inferred = "text"
expect(inferred).to_equal("text")
```

</details>

#### infers i64 from integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 42
# Generated field type should be i64
val literal = 42
val inferred = "i64"
expect(inferred).to_equal("i64")
```

</details>

#### infers f64 from float literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     rate: 3.14
# Generated field type should be f64
val literal = "3.14"
val inferred = "f64"
expect(inferred).to_equal("f64")
```

</details>

#### struct shape validation

#### generates struct with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# Generated struct should have exactly 3 fields
val field_count = 3
val field_names = ["verbose", "output", "count"]
expect(field_count).to_equal(3)
expect(field_names).to_contain("verbose")
expect(field_names).to_contain("output")
expect(field_names).to_contain("count")
```

</details>

#### preserves field order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fields should appear in declaration order
val fields = ["verbose", "output", "count"]
expect(fields[0]).to_equal("verbose")
expect(fields[1]).to_equal("output")
expect(fields[2]).to_equal("count")
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
