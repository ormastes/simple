# Validation Specification

> <details>

<!-- sdn-diagram:id=validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

validation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Specification

## Scenarios

### Content length validation

#### accepts zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(0)
expect(result).to_be_nil()
```

</details>

#### accepts normal length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(1000)
expect(result).to_be_nil()
```

</details>

#### rejects negative length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(-100)
match result:
    case nil: fail("negative content length should be rejected")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>

#### rejects excessive length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(2000000)
match result:
    case nil: fail("excessive content length should be rejected")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>

#### accepts at exact limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val limits = default_validation_limits()
val result = validator.validate_content_length(limits.max_content_length)
expect(result).to_be_nil()
```

</details>

### String length validation

#### accepts empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_string("")
expect(result).to_be_nil()
```

</details>

#### accepts normal string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_string("hello world")
expect(result).to_be_nil()
```

</details>

### URI scheme validation

#### accepts file URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("file:///home/user/test.spl")
expect(result).to_be_nil()
```

</details>

#### accepts symbol URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("symbol://project/MyClass")
expect(result).to_be_nil()
```

</details>

#### accepts project URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("project://myproject/src")
expect(result).to_be_nil()
```

</details>

#### accepts http URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("http://example.com/resource")
expect(result).to_be_nil()
```

</details>

#### accepts https URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("https://example.com/resource")
expect(result).to_be_nil()
```

</details>

#### rejects ftp URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("ftp://example.com/file")
match result:
    case nil: fail("ftp URI should be rejected")
    case err: expect(err.message.contains("scheme")).to_equal(true)
```

</details>

#### rejects invalid scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("invalid://test")
match result:
    case nil: fail("invalid URI scheme should be rejected")
    case err: expect(err.message.contains("scheme")).to_equal(true)
```

</details>

### URI emptiness validation

#### rejects empty URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("")
match result:
    case nil: fail("empty URI should be rejected")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

### Tool name validation

#### accepts simple name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("read_code")
expect(result).to_be_nil()
```

</details>

#### accepts name with hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("read-code")
expect(result).to_be_nil()
```

</details>

#### accepts name with slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tools/list")
expect(result).to_be_nil()
```

</details>

#### rejects empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("")
match result:
    case nil: fail("empty tool name should be rejected")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

### Array size validation

#### accepts zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(0)
expect(result).to_be_nil()
```

</details>

#### accepts normal size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(100)
expect(result).to_be_nil()
```

</details>

#### rejects negative size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(-10)
match result:
    case nil: fail("negative array length should be rejected")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>

#### rejects excessive size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(2000)
match result:
    case nil: fail("excessive array length should be rejected")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>

### Validation limits constants

#### has correct default content limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_content_length).to_equal(1048576)
```

</details>

#### has correct strict content limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
expect(limits.max_content_length).to_equal(524288)
```

</details>

#### has correct default string limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_string_length).to_equal(65536)
```

</details>

#### has correct strict string limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
expect(limits.max_string_length).to_equal(32768)
```

</details>

#### has correct default array limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_array_length).to_equal(1000)
```

</details>

#### has correct strict array limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
expect(limits.max_array_length).to_equal(500)
```

</details>

#### default is more permissive than strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = default_validation_limits()
val s = strict_validation_limits()
expect(d.max_content_length > s.max_content_length).to_equal(true)
expect(d.max_string_length > s.max_string_length).to_equal(true)
expect(d.max_array_length > s.max_array_length).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Content length validation
- String length validation
- URI scheme validation
- URI emptiness validation
- Tool name validation
- Array size validation
- Validation limits constants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
