# Testing Specification

> Tests covering Testing - test_parse(), Testing - test_parse_error(), Testing - test_validate(), Testing - test_const_eval(), Testing - test_no_const_eval(), Testing - mock_block(), Testing - Assertion Helpers, Testing - Integration, Testing - Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Testing Specification

## Scenarios

### Testing - test_parse()

#### accepts a valid block fixture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a valid block fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a valid block fixture")
check(fake_parse("valid parse"))
```

</details>

#### rejects an invalid block fixture

- rejects an invalid block fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid block fixture")
check(not fake_parse("broken parse"))
```

</details>

### Testing - test_parse_error()

#### returns no error for a valid block

- returns no error for a valid block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns no error for a valid block")
check_text(fake_parse_error("valid parse"), "")
```

</details>

#### returns an error message for invalid input

- returns an error message for invalid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an error message for invalid input")
check_text(fake_parse_error("broken parse"), "unexpected token")
```

</details>

### Testing - test_validate()

#### accepts the parse fixture

- accepts the parse fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the parse fixture")
check(fake_validate("valid parse"))
```

</details>

#### accepts the mock block fixture

- accepts the mock block fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the mock block fixture")
check(fake_validate("valid mock block"))
```

</details>

#### rejects an invalid fixture

- rejects an invalid fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid fixture")
check(not fake_validate("broken parse"))
```

</details>

### Testing - test_const_eval()

#### returns a const value for arithmetic

- returns a const value for arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a const value for arithmetic")
check_text(fake_const_eval("2 + 2"), "4")
```

</details>

#### returns an empty result for non-const input

- returns an empty result for non-const input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty result for non-const input")
check_text(fake_const_eval("x + 2"), "")
```

</details>

### Testing - test_no_const_eval()

#### reports empty output for non-const input

- reports empty output for non-const input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports empty output for non-const input")
check_text(fake_const_eval("side effect"), "")
```

</details>

### Testing - mock_block()

#### creates a named mock block

- creates a named mock block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a named mock block")
check_text(fake_mock_block("parse"), "parse block")
```

</details>

#### falls back to an unnamed mock block

- falls back to an unnamed mock block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to an unnamed mock block")
check_text(fake_mock_block(""), "unnamed block")
```

</details>

### Testing - Assertion Helpers

#### assert_parse_succeeds returns true for valid input

- assert_parse_succeeds returns true for valid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_parse_succeeds returns true for valid input")
check(fake_assert_parse_succeeds("valid parse"))
```

</details>

#### assert_parse_fails returns true for invalid input

- assert_parse_fails returns true for invalid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_parse_fails returns true for invalid input")
check(fake_assert_parse_fails("broken parse"))
```

</details>

#### assert_validation_passes returns true for valid input

- assert_validation_passes returns true for valid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_validation_passes returns true for valid input")
check(fake_assert_validation_passes("valid mock block"))
```

</details>

#### assert_validation_fails returns true for invalid input

- assert_validation_fails returns true for invalid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assert_validation_fails returns true for invalid input")
check(fake_assert_validation_fails("broken parse"))
```

</details>

### Testing - Integration

#### combines parse, validate, and mock block helpers

- combines parse, validate, and mock block helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines parse, validate, and mock block helpers")
val parsed = fake_assert_parse_succeeds("valid parse")
val validated = fake_assert_validation_passes("valid mock block")
val mock_name = fake_mock_block("parse")
check(parsed)
check(validated)
check_text(mock_name, "parse block")
```

</details>

#### keeps error and success paths separate

- keeps error and success paths separate


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps error and success paths separate")
val parse_ok = fake_assert_parse_succeeds("valid parse")
val parse_bad = fake_assert_parse_fails("broken parse")
check(parse_ok)
check(parse_bad)
```

</details>

### Testing - Edge Cases

#### handles empty payloads

- handles empty payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty payloads")
check(not fake_parse(""))
check_text(fake_parse_error(""), "unexpected token")
```

</details>

#### handles large payloads

- handles large payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large payloads")
val payload = "valid parse"
check(fake_parse(payload))
check(fake_validate(payload))
```

</details>

#### handles unicode in test names and labels

- handles unicode in test names and labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unicode in test names and labels")
check_text(fake_mock_block("unicode"), "unicode block")
```

</details>

#### handles complex error messages

- handles complex error messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles complex error messages")
check_text(fake_parse_error("broken parse"), "unexpected token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/blocks/testing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Testing - test_parse(), Testing - test_parse_error(), Testing - test_validate(), Testing - test_const_eval(), Testing - test_no_const_eval(), Testing - mock_block(), Testing - Assertion Helpers, Testing - Integration, Testing - Edge Cases.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e233fa89be03137f3c02bc9d90452d1243744a473d4a1dbfe6252a63c2e1f940`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e233fa89be03137f3c02bc9d90452d1243744a473d4a1dbfe6252a63c2e1f940`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e233fa89be03137f3c02bc9d90452d1243744a473d4a1dbfe6252a63c2e1f940`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/blocks/testing_spec.spl
mirror: doc/06_spec/01_unit/compiler/blocks/testing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/blocks/testing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/blocks/testing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/blocks/testing_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a valid block fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/blocks/testing_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid block fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/blocks/testing_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns no error for a valid block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
