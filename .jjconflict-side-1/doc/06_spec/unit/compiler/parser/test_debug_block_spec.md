# Test Debug Block Specification

> Tests covering builtin mode constants, __builtin_test_mode, __builtin_debug_mode, @test annotation desugaring, @debug annotation desugaring, mode independence.

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

- test_mode_is_bool: test mode is a boolean value
   - Expected: mode is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_mode_is_bool: test mode is a boolean value")
# In interpreter mode, test mode is false
val mode = false
expect(mode).to_equal(false)
```

</details>

#### test_mode_interpreter_default: defaults to false in interpreter

- test_mode_interpreter_default: defaults to false in interpreter
   - Expected: expected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_mode_interpreter_default: defaults to false in interpreter")
val expected = false
expect(expected).to_equal(false)
```

</details>

#### test_mode_if_block: code in test block is conditional

- test_mode_if_block: code in test block is conditional
   - Expected: ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_mode_if_block: code in test block is conditional")
var ran = false
if false:
    ran = true
expect(ran).to_equal(false)
```

</details>

### __builtin_debug_mode

#### debug_mode_is_bool: debug mode is a boolean value

- debug_mode_is_bool: debug mode is a boolean value
   - Expected: mode is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_mode_is_bool: debug mode is a boolean value")
val mode = false
expect(mode).to_equal(false)
```

</details>

#### debug_mode_interpreter_default: defaults to false in interpreter

- debug_mode_interpreter_default: defaults to false in interpreter
   - Expected: expected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_mode_interpreter_default: defaults to false in interpreter")
val expected = false
expect(expected).to_equal(false)
```

</details>

### @test annotation desugaring

#### test_block_desugars_to_if: @test desugars to if __builtin_test_mode

- test_block_desugars_to_if: @test desugars to if __builtin_test_mode
   - Expected: test_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_block_desugars_to_if: @test desugars to if __builtin_test_mode")
val test_mode = false
var test_ran = false
if test_mode:
    test_ran = true
expect(test_ran).to_equal(false)
```

</details>

#### test_block_name_is_string: @test takes a string name argument

- test_block_name_is_string: @test takes a string name argument
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_block_name_is_string: @test takes a string name argument")
val test_name = "my test"
val is_valid = test_name.len() > 0
expect(is_valid).to_equal(true)
```

</details>

#### test_block_enabled_runs: test code runs when mode is true

- test_block_enabled_runs: test code runs when mode is true
   - Expected: ran is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("test_block_enabled_runs: test code runs when mode is true")
val test_mode = true
var ran = false
if test_mode:
    ran = true
expect(ran).to_equal(true)
```

</details>

### @debug annotation desugaring

#### debug_block_desugars_to_if: @debug desugars to if __builtin_debug_mode

- debug_block_desugars_to_if: @debug desugars to if __builtin_debug_mode
   - Expected: debug_ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_block_desugars_to_if: @debug desugars to if __builtin_debug_mode")
val debug_mode = false
var debug_ran = false
if debug_mode:
    debug_ran = true
expect(debug_ran).to_equal(false)
```

</details>

#### debug_block_enabled_runs: debug code runs when mode is true

- debug_block_enabled_runs: debug code runs when mode is true
   - Expected: output equals `debug output`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_block_enabled_runs: debug code runs when mode is true")
val debug_mode = true
var output = "none"
if debug_mode:
    output = "debug output"
expect(output).to_equal("debug output")
```

</details>

#### debug_block_disabled_skips: debug code skipped when mode is false

- debug_block_disabled_skips: debug code skipped when mode is false
   - Expected: output equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_block_disabled_skips: debug code skipped when mode is false")
val debug_mode = false
var output = "none"
if debug_mode:
    output = "debug output"
expect(output).to_equal("none")
```

</details>

### mode independence

#### modes_are_independent: test_mode and debug_mode are separate

- modes_are_independent: test_mode and debug_mode are separate
   - Expected: test_mode equals `debug_mode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("modes_are_independent: test_mode and debug_mode are separate")
val test_mode = false
val debug_mode = false
expect(test_mode).to_equal(debug_mode)
```

</details>

#### mode_can_differ: one can be on while other is off

- mode_can_differ: one can be on while other is off
   - Expected: are_different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mode_can_differ: one can be on while other is off")
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
| Source | `test/unit/compiler/parser/test_debug_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering builtin mode constants, __builtin_test_mode, __builtin_debug_mode, @test annotation desugaring, @debug annotation desugaring, mode independence.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4997447c1c04812fa12edab6a8ac89b9b8a42145213c126b34294af2f80f5d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4997447c1c04812fa12edab6a8ac89b9b8a42145213c126b34294af2f80f5d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4997447c1c04812fa12edab6a8ac89b9b8a42145213c126b34294af2f80f5d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/test_debug_block_spec.spl
mirror: doc/06_spec/unit/compiler/parser/test_debug_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/test_debug_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/test_debug_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/test_debug_block_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test_mode_is_bool: test mode is a boolean value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/test_debug_block_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test_mode_interpreter_default: defaults to false in interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/test_debug_block_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test_mode_if_block: code in test block is conditional' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
