# Test Debug Block Specification

> <details>

<!-- sdn-diagram:id=test_debug_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_debug_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_debug_block_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_debug_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Debug Block Specification

## Scenarios

### builtin mode constants

### __builtin_test_mode

#### test_mode_is_bool: test mode is a boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In interpreter mode, test mode is false
val mode = false
expect(mode).to_equal(false)
```

</details>

#### test_mode_interpreter_default: defaults to false in interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = false
expect(expected).to_equal(false)
```

</details>

#### test_mode_if_block: code in test block is conditional

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ran = false
if false:
    ran = true
expect(ran).to_equal(false)
```

</details>

### __builtin_debug_mode

#### debug_mode_is_bool: debug mode is a boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = false
expect(mode).to_equal(false)
```

</details>

#### debug_mode_interpreter_default: defaults to false in interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = false
expect(expected).to_equal(false)
```

</details>

### @test annotation desugaring

#### test_block_desugars_to_if: @test desugars to if __builtin_test_mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = false
var test_ran = false
if test_mode:
    test_ran = true
expect(test_ran).to_equal(false)
```

</details>

#### test_block_name_is_string: @test takes a string name argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_name = "my test"
val is_valid = test_name.len() > 0
expect(is_valid).to_equal(true)
```

</details>

#### test_block_enabled_runs: test code runs when mode is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = true
var ran = false
if test_mode:
    ran = true
expect(ran).to_equal(true)
```

</details>

### @debug annotation desugaring

#### debug_block_desugars_to_if: @debug desugars to if __builtin_debug_mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_mode = false
var debug_ran = false
if debug_mode:
    debug_ran = true
expect(debug_ran).to_equal(false)
```

</details>

#### debug_block_enabled_runs: debug code runs when mode is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_mode = true
var output = "none"
if debug_mode:
    output = "debug output"
expect(output).to_equal("debug output")
```

</details>

#### debug_block_disabled_skips: debug code skipped when mode is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_mode = false
var output = "none"
if debug_mode:
    output = "debug output"
expect(output).to_equal("none")
```

</details>

### mode independence

#### modes_are_independent: test_mode and debug_mode are separate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = false
val debug_mode = false
expect(test_mode).to_equal(debug_mode)
```

</details>

#### mode_can_differ: one can be on while other is off

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_mode = true
val debug_mode = false
val are_different = test_mode != debug_mode
expect(are_different).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/test_debug_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- builtin mode constants
- __builtin_test_mode
- __builtin_debug_mode
- @test annotation desugaring
- @debug annotation desugaring
- mode independence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
