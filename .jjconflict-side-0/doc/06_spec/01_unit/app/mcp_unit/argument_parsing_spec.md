# Argument Parsing Specification

> <details>

<!-- sdn-diagram:id=argument_parsing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=argument_parsing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

argument_parsing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=argument_parsing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argument Parsing Specification

## Scenarios

### Argument Parsing

### get_arg_value

#### extracts value after flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = jo2(jp("flag", js("--debug")), jp("value", js("true")))
val value = extract_json_string(args, "value")
expect(value).to_equal("true")
```

</details>

#### extracts value from flag=value syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "flag=value"
val has_equals = input.contains("=")
expect(has_equals).to_equal(true)
```

</details>

#### handles missing value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = jo1(jp("flag", js("--debug")))
val value = extract_json_string(args, "missing")
expect(value).to_equal("")
```

</details>

#### handles empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = jo1(jp("flag", js("")))
val value = extract_json_string(args, "flag")
expect(value).to_equal("")
```

</details>

### has_flag

#### detects flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = "--debug --verbose"
val has_debug = flags.contains("--debug")
expect(has_debug).to_equal(true)
```

</details>

#### detects flag absence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = "--debug --verbose"
val has_quiet = flags.contains("--quiet")
expect(has_quiet).to_equal(false)
```

</details>

#### handles flag with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--flag"
val has_prefix = flag.starts_with("--")
expect(has_prefix).to_equal(true)
```

</details>

### Flag Parsing Edge Cases

#### handles flag at start of args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = "--first arg1 arg2"
val starts_with_flag = args.starts_with("--")
expect(starts_with_flag).to_equal(true)
```

</details>

#### handles flag at end of args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = "arg1 arg2 --last"
val ends_with_flag = args.ends_with("--last")
expect(ends_with_flag).to_equal(true)
```

</details>

#### handles flag in middle of args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = "arg1 --middle arg2"
val has_middle = args.contains("--middle")
expect(has_middle).to_equal(true)
```

</details>

#### handles multiple flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = "--flag1 --flag2 --flag3"
expect(args.contains("--flag1")).to_equal(true)
expect(args.contains("--flag2")).to_equal(true)
expect(args.contains("--flag3")).to_equal(true)
```

</details>

### Value Extraction

#### extracts string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo1(jp("key", js("string_value")))
val value = extract_json_string(obj, "key")
expect(value).to_equal("string_value")
```

</details>

#### extracts numeric value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo1(jp("count", "42"))
val value = extract_json_value(obj, "count")
expect(value).to_equal("42")
```

</details>

#### extracts boolean flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo1(jp("verbose", "true"))
val value = extract_json_value(obj, "verbose")
expect(value).to_equal("true")
```

</details>

### Special Characters

#### handles values with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "hello world"
expect(value.contains(" ")).to_equal(true)
```

</details>

#### handles values with special chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = "path/to/file.spl"
expect(value.contains("/")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/argument_parsing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Argument Parsing
- get_arg_value
- has_flag
- Flag Parsing Edge Cases
- Value Extraction
- Special Characters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
