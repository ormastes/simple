# Serialization SDN Format Coverage Specification

> Branch-coverage tests for SDN format functions, format detection, and pretty printing:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 49 | 49 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization SDN Format Coverage Specification

Branch-coverage tests for SDN format functions, format detection, and pretty printing:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SERIAL-COV-SDN |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/common/serialization_sdn_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Branch-coverage tests for SDN format functions, format detection, and pretty printing:
- to_sdn_* functions (formats.spl)
- detect_format, is_numeric_text, is_valid_sdn (formats.spl)
- pretty_print_indent, pretty_list, pretty_tuple, pretty_dict (utilities.spl)

## Scenarios

### to_sdn_int

#### converts positive integer

- converts positive integer
   - Expected: to_sdn_int(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts positive integer")
expect(to_sdn_int(42)).to_equal("42")
```

</details>

#### converts zero

- converts zero
   - Expected: to_sdn_int(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts zero")
expect(to_sdn_int(0)).to_equal("0")
```

</details>

#### converts negative integer

- converts negative integer
   - Expected: to_sdn_int(-5) equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts negative integer")
expect(to_sdn_int(-5)).to_equal("-5")
```

</details>

### to_sdn_bool

#### converts true

- converts true
   - Expected: to_sdn_bool(true) equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts true")
expect(to_sdn_bool(true)).to_equal("true")
```

</details>

#### converts false

- converts false
   - Expected: to_sdn_bool(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts false")
expect(to_sdn_bool(false)).to_equal("false")
```

</details>

### to_sdn_nil

#### converts nil value

- converts nil value
   - Expected: to_sdn_nil() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nil value")
expect(to_sdn_nil()).to_equal("nil")
```

</details>

### to_sdn_text

#### quotes text

- quotes text
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes text")
val result = to_sdn_text("hello")
expect(result).to_equal("\"hello\"")
```

</details>

### to_sdn_list

#### converts empty list

- converts empty list
   - Expected: to_sdn_list([]) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty list")
expect(to_sdn_list([])).to_equal("[]")
```

</details>

#### converts non-empty list

- converts non-empty list
   - Expected: to_sdn_list(["1", "2"]) equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts non-empty list")
expect(to_sdn_list(["1", "2"])).to_equal("[1, 2]")
```

</details>

### to_sdn_tuple

#### converts empty tuple

- converts empty tuple
   - Expected: to_sdn_tuple([]) equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty tuple")
expect(to_sdn_tuple([])).to_equal("()")
```

</details>

#### converts non-empty tuple

- converts non-empty tuple
   - Expected: to_sdn_tuple(["a", "b"]) equals `(a, b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts non-empty tuple")
expect(to_sdn_tuple(["a", "b"])).to_equal("(a, b)")
```

</details>

### to_sdn_dict

#### converts empty dict

- converts empty dict
   - Expected: to_sdn_dict([]) equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts empty dict")
expect(to_sdn_dict([])).to_equal("{}")
```

</details>

#### converts non-empty dict

- converts non-empty dict
   - Expected: to_sdn_dict([("k", "v")]) equals `{k: v}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts non-empty dict")
expect(to_sdn_dict([("k", "v")])).to_equal("{k: v}")
```

</details>

### is_numeric_text

#### returns false for empty string

- returns false for empty string
   - Expected: is_numeric_text("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty string")
expect(is_numeric_text("")).to_equal(false)
```

</details>

#### returns false for minus sign only

- returns false for minus sign only
   - Expected: is_numeric_text("-") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for minus sign only")
expect(is_numeric_text("-")).to_equal(false)
```

</details>

#### returns true for single digit

- returns true for single digit
   - Expected: is_numeric_text("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for single digit")
expect(is_numeric_text("5")).to_equal(true)
```

</details>

#### returns true for multi-digit number

- returns true for multi-digit number
   - Expected: is_numeric_text("12345") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for multi-digit number")
expect(is_numeric_text("12345")).to_equal(true)
```

</details>

#### returns true for negative number

- returns true for negative number
   - Expected: is_numeric_text("-42") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for negative number")
expect(is_numeric_text("-42")).to_equal(true)
```

</details>

#### returns false for alphabetic text

- returns false for alphabetic text
   - Expected: is_numeric_text("abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for alphabetic text")
expect(is_numeric_text("abc")).to_equal(false)
```

</details>

#### returns false for mixed text

- returns false for mixed text
   - Expected: is_numeric_text("12a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for mixed text")
expect(is_numeric_text("12a")).to_equal(false)
```

</details>

#### returns true for zero

- returns true for zero
   - Expected: is_numeric_text("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for zero")
expect(is_numeric_text("0")).to_equal(true)
```

</details>

### detect_format

#### returns unknown for empty string

- returns unknown for empty string
   - Expected: detect_format("") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for empty string")
expect(detect_format("")).to_equal("unknown")
```

</details>

#### detects tagged format

- detects tagged format
   - Expected: detect_format("@MyType\{payload\}") equals `tagged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects tagged format")
expect(detect_format("@MyType\{payload\}")).to_equal("tagged")
```

</details>

#### detects sdn for dict starting with brace

- detects sdn for dict starting with brace
   - Expected: detect_format("{key: val}") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for dict starting with brace")
expect(detect_format("{key: val}")).to_equal("sdn")
```

</details>

#### detects sdn for list starting with bracket

- detects sdn for list starting with bracket
   - Expected: detect_format("[1, 2, 3]") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for list starting with bracket")
expect(detect_format("[1, 2, 3]")).to_equal("sdn")
```

</details>

#### detects sdn for quoted string

- detects sdn for quoted string
   - Expected: detect_format("\"hello\"") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for quoted string")
expect(detect_format("\"hello\"")).to_equal("sdn")
```

</details>

#### detects sdn for true

- detects sdn for true
   - Expected: detect_format("true") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for true")
expect(detect_format("true")).to_equal("sdn")
```

</details>

#### detects sdn for false

- detects sdn for false
   - Expected: detect_format("false") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for false")
expect(detect_format("false")).to_equal("sdn")
```

</details>

#### detects sdn for nil

- detects sdn for nil
   - Expected: detect_format("nil") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for nil")
expect(detect_format("nil")).to_equal("sdn")
```

</details>

#### detects sdn for numeric string

- detects sdn for numeric string
   - Expected: detect_format("42") equals `sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects sdn for numeric string")
expect(detect_format("42")).to_equal("sdn")
```

</details>

#### returns unknown for unrecognized format

- returns unknown for unrecognized format
   - Expected: detect_format("random_text") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for unrecognized format")
expect(detect_format("random_text")).to_equal("unknown")
```

</details>

### is_valid_sdn

#### returns true for valid sdn list

- returns true for valid sdn list
   - Expected: is_valid_sdn("[1, 2]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for valid sdn list")
expect(is_valid_sdn("[1, 2]")).to_equal(true)
```

</details>

#### returns true for tagged format

- returns true for tagged format
   - Expected: is_valid_sdn("@Type\{payload\}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for tagged format")
expect(is_valid_sdn("@Type\{payload\}")).to_equal(true)
```

</details>

#### returns true for sdn boolean

- returns true for sdn boolean
   - Expected: is_valid_sdn("true") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for sdn boolean")
expect(is_valid_sdn("true")).to_equal(true)
```

</details>

#### returns false for invalid input

- returns false for invalid input
   - Expected: is_valid_sdn("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for invalid input")
expect(is_valid_sdn("")).to_equal(false)
```

</details>

#### returns false for unknown format

- returns false for unknown format
   - Expected: is_valid_sdn("random_text") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown format")
expect(is_valid_sdn("random_text")).to_equal(false)
```

</details>

### pretty_print_indent

#### adds no indent at level 0

- adds no indent at level 0
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds no indent at level 0")
val result = pretty_print_indent("hello", 0)
expect(result).to_equal("hello")
```

</details>

#### adds two spaces per indent level

- adds two spaces per indent level


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two spaces per indent level")
val result = pretty_print_indent("hello", 2)
expect(result).to_start_with("    ")
expect(result).to_end_with("hello")
```

</details>

#### adds single level indent

- adds single level indent
   - Expected: result equals `  x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds single level indent")
val result = pretty_print_indent("x", 1)
expect(result).to_equal("  x")
```

</details>

### pretty_list

#### returns bracket pair for empty list

- returns bracket pair for empty list
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bracket pair for empty list")
val result = pretty_list([], 0)
expect(result).to_equal("[]")
```

</details>

#### formats single item list

- formats single item list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats single item list")
val result = pretty_list(["a"], 0)
expect(result).to_start_with("[\n")
expect(result).to_contain("a")
```

</details>

#### formats multi-item list with commas

- formats multi-item list with commas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats multi-item list with commas")
val result = pretty_list(["a", "b"], 0)
expect(result).to_contain(",")
```

</details>

#### does not add comma after last item

- does not add comma after last item


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not add comma after last item")
val result = pretty_list(["a"], 0)
expect(result).to_contain("a\n")
```

</details>

### pretty_tuple

#### returns parens for empty tuple

- returns parens for empty tuple
   - Expected: result equals `()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns parens for empty tuple")
val result = pretty_tuple([], 0)
expect(result).to_equal("()")
```

</details>

#### formats single value tuple

- formats single value tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats single value tuple")
val result = pretty_tuple(["x"], 0)
expect(result).to_start_with("(\n")
expect(result).to_contain("x")
```

</details>

#### formats multi-value tuple with commas

- formats multi-value tuple with commas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats multi-value tuple with commas")
val result = pretty_tuple(["x", "y"], 0)
expect(result).to_contain(",")
```

</details>

### pretty_dict

#### returns braces for empty dict

- returns braces for empty dict
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns braces for empty dict")
val result = pretty_dict([], 0)
expect(result).to_equal("{}")
```

</details>

#### formats single entry dict

- formats single entry dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats single entry dict")
val result = pretty_dict([("k", "v")], 0)
expect(result).to_start_with("{\n")
expect(result).to_contain("k: v")
```

</details>

#### formats multi-entry dict with commas

- formats multi-entry dict with commas


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats multi-entry dict with commas")
val result = pretty_dict([("a", "1"), ("b", "2")], 0)
expect(result).to_contain(",")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 49 |
| Active scenarios | 49 |
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

- Canonical SPipe generation for source `ceed19d60a7982121626aaea34c17427dda6ae8e1bc9fd98a505a724ae4468de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ceed19d60a7982121626aaea34c17427dda6ae8e1bc9fd98a505a724ae4468de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ceed19d60a7982121626aaea34c17427dda6ae8e1bc9fd98a505a724ae4468de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/serialization_sdn_format_spec.spl
mirror: doc/06_spec/01_unit/lib/common/serialization_sdn_format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/serialization_sdn_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/serialization_sdn_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/serialization_sdn_format_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts positive integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/serialization_sdn_format_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/serialization_sdn_format_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts negative integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
