# CLI Args Type Inference Specification

> Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from its default value: bool from true/false, text from string literals, i64 from integers, f64 from floats, and arrays from array literals.

<!-- sdn-diagram:id=cli_args_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Type Inference Specification

Tests type inference from default values in the `cli` keyword block. The compiler infers the type of each option from its default value: bool from true/false, text from string literals, i64 from integers, f64 from floats, and arrays from array literals.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-002 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests type inference from default values in the `cli` keyword block.
The compiler infers the type of each option from its default value:
bool from true/false, text from string literals, i64 from integers,
f64 from floats, and arrays from array literals.

## Syntax

```simple
cli:
    flag: false           # inferred as bool
    name: "default"       # inferred as text
    count: 0              # inferred as i64
    rate: 0.5             # inferred as f64
    tags: ["a", "b"]      # inferred as [text]
```

## Scenarios

### CLI Args Type Inference

#### bool inference

#### infers bool from false default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# Type of args.verbose should be bool
val inferred_type = "bool"
expect(inferred_type).to_equal("bool")
```

</details>

#### infers bool from true default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     debug: true
# Type of args.debug should be bool
val inferred_type = "bool"
expect(inferred_type).to_equal("bool")
```

</details>

#### text inference

#### infers text from string default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "result.txt"
# Type of args.output should be text
val inferred_type = "text"
expect(inferred_type).to_equal("text")
```

</details>

#### handles empty string default

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     name: ""
# Type of args.name should be text, value is ""
val default_val = ""
val inferred_type = "text"
expect(default_val).to_equal("")
expect(inferred_type).to_equal("text")
```

</details>

#### numeric inference

#### infers i64 from int default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 10
# Type of args.count should be i64
val inferred_type = "i64"
expect(inferred_type).to_equal("i64")
```

</details>

#### infers f64 from float default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     rate: 0.5
# Type of args.rate should be f64
val inferred_type = "f64"
expect(inferred_type).to_equal("f64")
```

</details>

#### handles zero int default

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     offset: 0
# Type should be i64, value is 0
val default_val = 0
val inferred_type = "i64"
expect(default_val).to_equal(0)
expect(inferred_type).to_equal("i64")
```

</details>

#### array inference

#### infers array from array default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     tags: ["dev", "test"]
# Type of args.tags should be [text]
val inferred_type = "[text]"
expect(inferred_type).to_equal("[text]")
```

</details>

#### struct generation

#### preserves type across parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 42
# val args = cli.parse(["--count", "100"])
# typeof(args.count) should still be i64
val original_type = "i64"
val parsed_type = "i64"
expect(original_type).to_equal(parsed_type)
```

</details>

#### generates correct struct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
#     output: "out.txt"
#     count: 1
# Generated struct should have fields: verbose: bool, output: text, count: i64
val fields = ["verbose: bool", "output: text", "count: i64"]
expect(fields[0]).to_contain("bool")
expect(fields.len()).to_equal(3)
expect(fields[1]).to_contain("text")
expect(fields[2]).to_contain("i64")
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
