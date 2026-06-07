# Testing Specification

> 1. check

<!-- sdn-diagram:id=testing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=testing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

testing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=testing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Testing Specification

## Scenarios

### Testing - test_parse()

#### accepts a valid block fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_parse("valid parse"))
```

</details>

#### rejects an invalid block fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not fake_parse("broken parse"))
```

</details>

### Testing - test_parse_error()

#### returns no error for a valid block

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_parse_error("valid parse"), "")
```

</details>

#### returns an error message for invalid input

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_parse_error("broken parse"), "unexpected token")
```

</details>

### Testing - test_validate()

#### accepts the parse fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_validate("valid parse"))
```

</details>

#### accepts the mock block fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_validate("valid mock block"))
```

</details>

#### rejects an invalid fixture

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not fake_validate("broken parse"))
```

</details>

### Testing - test_const_eval()

#### returns a const value for arithmetic

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_const_eval("2 + 2"), "4")
```

</details>

#### returns an empty result for non-const input

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_const_eval("x + 2"), "")
```

</details>

### Testing - test_no_const_eval()

#### reports empty output for non-const input

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_const_eval("side effect"), "")
```

</details>

### Testing - mock_block()

#### creates a named mock block

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_mock_block("parse"), "parse block")
```

</details>

#### falls back to an unnamed mock block

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_mock_block(""), "unnamed block")
```

</details>

### Testing - Assertion Helpers

#### assert_parse_succeeds returns true for valid input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_assert_parse_succeeds("valid parse"))
```

</details>

#### assert_parse_fails returns true for invalid input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_assert_parse_fails("broken parse"))
```

</details>

#### assert_validation_passes returns true for valid input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_assert_validation_passes("valid mock block"))
```

</details>

#### assert_validation_fails returns true for invalid input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(fake_assert_validation_fails("broken parse"))
```

</details>

### Testing - Integration

#### combines parse, validate, and mock block helpers

1. check
2. check
3. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = fake_assert_parse_succeeds("valid parse")
val validated = fake_assert_validation_passes("valid mock block")
val mock_name = fake_mock_block("parse")
check(parsed)
check(validated)
check_text(mock_name, "parse block")
```

</details>

#### keeps error and success paths separate

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parse_ok = fake_assert_parse_succeeds("valid parse")
val parse_bad = fake_assert_parse_fails("broken parse")
check(parse_ok)
check(parse_bad)
```

</details>

### Testing - Edge Cases

#### handles empty payloads

1. check
2. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not fake_parse(""))
check_text(fake_parse_error(""), "unexpected token")
```

</details>

#### handles large payloads

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = "valid parse"
check(fake_parse(payload))
check(fake_validate(payload))
```

</details>

#### handles unicode in test names and labels

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_mock_block("unicode"), "unicode block")
```

</details>

#### handles complex error messages

1. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_text(fake_parse_error("broken parse"), "unexpected token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/blocks/testing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Testing - test_parse()
- Testing - test_parse_error()
- Testing - test_validate()
- Testing - test_const_eval()
- Testing - test_no_const_eval()
- Testing - mock_block()
- Testing - Assertion Helpers
- Testing - Integration
- Testing - Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
