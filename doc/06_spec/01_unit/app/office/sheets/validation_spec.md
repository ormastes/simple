# Validation Specification

> Tests covering validation list rules, validation whole_number rules, validation decimal rules, validation text_length rules, validation date rules, validation remove, validate_sheet, validation column-wide rules, validation_list_values, validation deliberate-fail probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Specification

## Scenarios

### validation list rules

#### accepts member in allowed list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "apple,banana,cherry", 0.0, 0.0, "", "Not in list")
val result = validation_check(rules, Sheet.new("test"), "A1", "banana")
expect(result.ok).to_equal(true)
```

</details>

#### rejects non-member with message

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "apple,banana,cherry", 0.0, 0.0, "", "Must be apple, banana, or cherry")
val result = validation_check(rules, Sheet.new("test"), "A1", "orange")
expect(result.ok).to_equal(false)
expect(result.message).to_equal("Must be apple, banana, or cherry")
```

</details>

### validation whole_number rules

#### accepts value at minimum boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "B1", "whole_number", "", 10.0, 20.0, "", "Must be 10-20")
val result = validation_check(rules, Sheet.new("test"), "B1", "10")
expect(result.ok).to_equal(true)
```

</details>

#### rejects value below minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "B1", "whole_number", "", 10.0, 20.0, "", "Must be 10-20")
val result = validation_check(rules, Sheet.new("test"), "B1", "9")
expect(result.ok).to_equal(false)
```

</details>

#### accepts value at maximum boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "B1", "whole_number", "", 10.0, 20.0, "", "Must be 10-20")
val result = validation_check(rules, Sheet.new("test"), "B1", "20")
expect(result.ok).to_equal(true)
```

</details>

#### rejects non-integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "B1", "whole_number", "", 10.0, 20.0, "", "Must be integer")
val result = validation_check(rules, Sheet.new("test"), "B1", "15.5")
expect(result.ok).to_equal(false)
```

</details>

### validation decimal rules

#### accepts decimal within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "C1", "decimal", "", 0.5, 2.5, "", "Must be 0.5-2.5")
val result = validation_check(rules, Sheet.new("test"), "C1", "1.5")
expect(result.ok).to_equal(true)
```

</details>

#### rejects decimal above maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "C1", "decimal", "", 0.5, 2.5, "", "Must be 0.5-2.5")
val result = validation_check(rules, Sheet.new("test"), "C1", "3.0")
expect(result.ok).to_equal(false)
```

</details>

### validation text_length rules

#### accepts text within length bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "D1", "text_length", "", 3.0, 10.0, "", "Must be 3-10 chars")
val result = validation_check(rules, Sheet.new("test"), "D1", "hello")
expect(result.ok).to_equal(true)
```

</details>

#### rejects text shorter than minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "D1", "text_length", "", 3.0, 10.0, "", "Must be 3-10 chars")
val result = validation_check(rules, Sheet.new("test"), "D1", "ab")
expect(result.ok).to_equal(false)
```

</details>

#### rejects text longer than maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "D1", "text_length", "", 3.0, 10.0, "", "Must be 3-10 chars")
val result = validation_check(rules, Sheet.new("test"), "D1", "this is too long")
expect(result.ok).to_equal(false)
```

</details>

### validation date rules

#### accepts date serial within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "E1", "date", "", 44562.0, 45000.0, "", "Invalid date range")
val result = validation_check(rules, Sheet.new("test"), "E1", "44700")
expect(result.ok).to_equal(true)
```

</details>

#### rejects date serial outside range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "E1", "date", "", 44562.0, 45000.0, "", "Invalid date range")
val result = validation_check(rules, Sheet.new("test"), "E1", "45100")
expect(result.ok).to_equal(false)
```

</details>

### validation remove

#### removes a rule by cell reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "apple,banana", 0.0, 0.0, "", "Bad list")
expect(rules.keys.len()).to_equal(1)
rules = validation_remove(rules, "A1")
expect(rules.keys.len()).to_equal(0)
```

</details>

#### does not affect other rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "apple", 0.0, 0.0, "", "Bad")
rules = validation_add(rules, "B1", "whole_number", "", 1.0, 10.0, "", "Bad")
rules = validation_remove(rules, "A1")
expect(rules.keys.len()).to_equal(1)
expect(rules.keys[0]).to_equal("B1")
```

</details>

### validate_sheet

#### returns all violations on a seeded sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("test")
sh.set_value("A1", "good")
sh.set_value("A2", "bad")
sh.set_value("B1", "150")
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "good,ok,fine", 0.0, 0.0, "", "Not in list")
rules = validation_add(rules, "A2", "list", "good,ok,fine", 0.0, 0.0, "", "Not in list")
rules = validation_add(rules, "B1", "whole_number", "", 0.0, 100.0, "", "Out of range")
val violations = validate_sheet(rules, sh)
expect(violations.len()).to_equal(2)
var saw_a2 = false
var saw_b1 = false
for violation in violations:
    if violation.ref == "A2":
        saw_a2 = violation.message == "Not in list"
    if violation.ref == "B1":
        saw_b1 = violation.message == "Out of range"
expect(saw_a2).to_equal(true)
expect(saw_b1).to_equal(true)
```

</details>

### validation column-wide rules

#### applies rule to every cell in column

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("test")
sh.set_value("A1", "10")
sh.set_value("A2", "20")
sh.set_value("A3", "5")
var rules = empty_validation_rules()
rules = validation_add(rules, "A", "whole_number", "", 10.0, 30.0, "", "Out of range")
val r1 = validation_check(rules, sh, "A1", "10")
val r2 = validation_check(rules, sh, "A2", "20")
val r3 = validation_check(rules, sh, "A3", "5")
expect(r1.ok).to_equal(true)
expect(r2.ok).to_equal(true)
expect(r3.ok).to_equal(false)
```

</details>

### validation_list_values

#### extracts allowed values from list rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "A1", "list", "apple, banana, cherry", 0.0, 0.0, "", "")
val values = validation_list_values(rules, "A1")
expect(values.len()).to_equal(3)
expect(values[0]).to_equal("apple")
expect(values[1]).to_equal("banana")
expect(values[2]).to_equal("cherry")
```

</details>

### validation deliberate-fail probe

#### fails when condition is wrong to verify test execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rules = empty_validation_rules()
rules = validation_add(rules, "Z1", "list", "x,y,z", 0.0, 0.0, "", "Not in xyz")
val result = validation_check(rules, Sheet.new("test"), "Z1", "w")
expect(result.ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/validation_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering validation list rules, validation whole_number rules, validation decimal rules, validation text_length rules, validation date rules, validation remove, validate_sheet, validation column-wide rules, validation_list_values, validation deliberate-fail probe.
- validation list rules
- validation whole_number rules
- validation decimal rules
- validation text_length rules
- validation date rules
- validation remove
- validate_sheet
- validation column-wide rules
- validation_list_values
- validation deliberate-fail probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
