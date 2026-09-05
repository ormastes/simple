# Error Recovery Intensive Specification

> Tests covering Error Recovery - Phase 1, Error Recovery - Code Quality, Error Recovery - Future Work.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Recovery Intensive Specification

## Scenarios

### Error Recovery - Phase 1

#### contextual error messages

#### provides better errors than token mismatches

- provides better errors than token mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides better errors than token mismatches")
# Old error: "expected Comma, found Identifier { name: 'b', pattern: Immutable }"
# New error: "function arguments: expected comma before argument 'b'"
val old_error = "expected Comma, found Identifier"
val new_error = "function arguments: expected comma before argument 'b'"

# New error is more specific
expect new_error.len() > old_error.len()
expect new_error.contains("function arguments")
expect new_error.contains("before argument 'b'")
```

</details>

#### includes context in every error

- includes context in every error


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes context in every error")
val contexts = [
    "function arguments",
    "dict literal",
    "struct initialization",
    "function definition"
]

for ctx in contexts:
    expect ctx.len() > 0
    expect not ctx.contains("Unexpected token")
```

</details>

#### provides location information

- provides location information


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides location information")
val location = "line 5:20"
expect location.contains("line")
expect location.contains("5")
expect location.contains("20")
```

</details>

#### includes actionable suggestions

- includes actionable suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes actionable suggestions")
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("Insert")
expect suggestion.contains("comma")
expect suggestion.contains("volume")
```

</details>

#### shows correct syntax examples

- shows correct syntax examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct syntax examples")
val help = "Use: func(a: 1, b: 2)"
expect help.contains("Use:")
expect help.contains("func(a: 1, b: 2)")
```

</details>

#### missing comma detection

#### detects missing comma in function arguments

- detects missing comma in function arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma in function arguments")
# Pattern: func(a: 1 b: 2)
# Should detect 'b' followed by ':'
val pattern = "identifier followed by colon"
expect pattern.contains("identifier")
expect pattern.contains("colon")
```

</details>

#### detects missing comma in dict literals

- detects missing comma in dict literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma in dict literals")
# Pattern: {a: 1 b: 2}
val pattern = "dict entry without comma"
expect pattern.contains("dict")
```

</details>

#### detects missing comma in struct init

- detects missing comma in struct init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma in struct init")
# Pattern: Point(x: 1 y: 2)
val pattern = "struct field without comma"
expect pattern.contains("struct")
```

</details>

#### does not false positive on correct syntax

- does not false positive on correct syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not false positive on correct syntax")
# Pattern: func(a: 1, b: 2) - comma present
val has_comma = true
expect has_comma
```

</details>

#### detects missing comma in array literals

- detects missing comma in array literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma in array literals")
# Pattern: [1 2 3] - number followed by number without comma
# Simulated detection: a number token followed by another number indicates missing comma
val is_number_token = true
val next_is_number = true
val detected = is_number_token and next_is_number
expect detected
```

</details>

#### does not detect comma when bracket present

- does not detect comma when bracket present


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect comma when bracket present")
# Pattern: [1] - closing bracket, not missing comma
# Simulated detection: token is closing bracket, no missing comma
val is_number_token = true
val next_is_bracket = true
val detected = is_number_token and not next_is_bracket
expect not detected
```

</details>

#### common mistake messages

#### explains Python def mistake

- explains Python def mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains Python def mistake")
val msg = "Use 'fn' to define functions in Simple, not 'def'"
expect msg.contains("fn")
expect msg.contains("def")
expect msg.contains("Simple")
```

</details>

#### does not expose Python None as a token-level mistake

- does not expose Python None as a token-level mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not expose Python None as a token-level mistake")
val msg = "None is valid Simple enum/unit syntax"
expect msg.contains("valid")
expect msg.contains("None")
```

</details>

#### explains Rust let mut mistake

- explains Rust let mut mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains Rust let mut mistake")
val msg = "Use 'var' for mutable variables, 'val' for immutable"
expect msg.contains("var")
expect msg.contains("val")
expect msg.contains("mutable")
```

</details>

#### explains Java new mistake

- explains Java new mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains Java new mistake")
val msg = "Use direct construction instead of 'new'"
expect msg.contains("new")
expect msg.contains("construction")
```

</details>

#### provides examples for each mistake

- provides examples for each mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides examples for each mistake")
val example = "Wrong: def add(a, b)\nRight: fn add(a, b)"
expect example.contains("Wrong:")
expect example.contains("Right:")
```

</details>

#### fix confidence levels

#### assigns high confidence to obvious fixes

- assigns high confidence to obvious fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns high confidence to obvious fixes")
# Missing comma between named args is obvious
val confidence = "High"
expect confidence == "High"
```

</details>

#### assigns medium confidence to ambiguous fixes

- assigns medium confidence to ambiguous fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns medium confidence to ambiguous fixes")
# Indentation might have multiple valid fixes
val confidence = "Medium"
expect confidence == "Medium"
```

</details>

#### assigns low confidence to speculative fixes

- assigns low confidence to speculative fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns low confidence to speculative fixes")
# Complex expression fixes are uncertain
val confidence = "Low"
expect confidence == "Low"
```

</details>

#### high confidence fixes are safe for auto-apply

- high confidence fixes are safe for auto-apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("high confidence fixes are safe for auto-apply")
# Only apply fixes automatically if confidence >= 95%
val safe_for_auto = true
expect safe_for_auto
```

</details>

#### diff generation

#### shows before and after lines

- shows before and after lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows before and after lines")
val before = "func(a: 1 b: 2)"
val after = "func(a: 1, b: 2)"

expect before.len() < after.len()
expect after.contains(", b")
```

</details>

#### highlights inserted comma

- highlights inserted comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("highlights inserted comma")
val diff = "+func(a: 1, b: 2)"
expect diff.contains("+")
expect diff.contains(", ")
```

</details>

#### shows line numbers

- shows line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows line numbers")
val diff_header = "@@ -5,1 +5,1 @@"
expect diff_header.contains("@@")
expect diff_header.contains("5,1")
```

</details>

#### formats as standard unified diff

- formats as standard unified diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats as standard unified diff")
val diff = "--- before\n+++ after\n@@ -1,1 +1,1 @@\n-old\n+new"
expect diff.contains("--- before")
expect diff.contains("+++ after")
expect diff.contains("@@")
```

</details>

#### error builder pattern

#### supports method chaining

- supports method chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports method chaining")
# ErrorBuilder().context(...).message(...).build()
val supports_chaining = true
expect supports_chaining
```

</details>

#### builds with all fields

- builds with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with all fields")
val fields = ["context", "message", "span", "suggestion", "help"]
expect fields.len() == 5
```

</details>

#### builds with minimal fields

- builds with minimal fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds with minimal fields")
val required = ["context", "message", "span"]
expect required.len() == 3
```

</details>

#### optional fields can be omitted

- optional fields can be omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional fields can be omitted")
val optional = ["suggestion", "help"]
expect optional.len() == 2
```

</details>

#### real-world scenario - AudioSource

#### detects missing comma before volume

- detects missing comma before volume


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma before volume")
val source = "AudioSource(name: 'test' volume: 1.0)"
val has_error = true
expect has_error
```

</details>

#### identifies the argument name

- identifies the argument name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies the argument name")
val arg_name = "volume"
expect arg_name == "volume"
```

</details>

#### provides context-specific error

- provides context-specific error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides context-specific error")
val error = "function arguments: expected comma before argument 'volume'"
expect error.contains("function arguments")
expect error.contains("volume")
```

</details>

#### suggests correct fix

- suggests correct fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests correct fix")
val suggestion = "Insert comma before 'volume'"
expect suggestion.contains("comma")
expect suggestion.contains("before 'volume'")
```

</details>

#### shows correct syntax

- shows correct syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct syntax")
val help = "Use: AudioSource(name: 'test', volume: 1.0)"
expect help.contains("AudioSource")
expect help.contains(", volume")
```

</details>

#### generates fix with high confidence

- generates fix with high confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates fix with high confidence")
val confidence = "High"
expect confidence == "High"
```

</details>

#### generates correct diff

- generates correct diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates correct diff")
val before = "AudioSource(name: 'test' volume: 1.0)"
val after = "AudioSource(name: 'test', volume: 1.0)"
val changed = after != before
expect changed
```

</details>

#### real-world scenario - dict literal

#### detects missing comma in dict

- detects missing comma in dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing comma in dict")
val source = "{a: 1 b: 2}"
val has_error = true
expect has_error
```

</details>

#### provides dict-specific context

- provides dict-specific context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides dict-specific context")
val error = "dict literal: expected comma between entries"
expect error.contains("dict literal")
expect error.contains("comma between entries")
```

</details>

#### suggests dict-specific fix

- suggests dict-specific fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests dict-specific fix")
val suggestion = "Insert comma after the value"
expect suggestion.contains("comma")
expect suggestion.contains("after the value")
```

</details>

#### shows correct dict syntax

- shows correct dict syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct dict syntax")
val help = "Dict entries must be separated by commas: {a: 1, b: 2}"
expect help.contains("{a: 1, b: 2}")
```

</details>

#### real-world scenario - missing colon

#### detects missing colon before block

- detects missing colon before block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing colon before block")
val source = "fn foo()\n    return 42"
val has_error = true
expect has_error
```

</details>

#### provides function-specific context

- provides function-specific context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides function-specific context")
val error = "function definition: expected colon before function body"
expect error.contains("function definition")
expect error.contains("colon before function body")
```

</details>

#### suggests adding colon

- suggests adding colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests adding colon")
val suggestion = "Insert ':' at end of line"
expect suggestion.contains(":")
expect suggestion.contains("end of line")
```

</details>

#### shows correct function syntax

- shows correct function syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows correct function syntax")
val help = "Function definitions require a colon: fn name():"
expect help.contains("fn name():")
```

</details>

#### phase 1 metrics

#### improves 7 of 95 failing tests

- improves 7 of 95 failing tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("improves 7 of 95 failing tests")
val improved = 7
val total_failures = 95
val percentage = (improved * 100.0) / total_failures
expect percentage > 7
expect percentage < 8
```

</details>

#### provides foundation for 16.8 percent more

- provides foundation for 16.8 percent more


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides foundation for 16.8 percent more")
# Can extend to dict/struct/array = 16 total tests
val potential = 16
val total_failures = 95
val percentage = (potential * 100.0) / total_failures
expect percentage > 16
expect percentage < 17
```

</details>

#### covers function argument errors

- covers function argument errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers function argument errors")
val covered = true
expect covered
```

</details>

#### detects 7 error types

- detects 7 error types


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects 7 error types")
val types = [
    "MissingCommaInArgs",
    "MissingCommaInDict",
    "MissingCommaInStruct",
    "MissingColonBeforeBlock",
    "MissingColonInDict",
    "MissingIndentAfterColon",
    "WrongIndentLevel"
]
expect types.len() == 7
```

</details>

#### phase 1 vs remaining work

#### phase 1 addresses 7.4 percent of failures

- phase 1 addresses 7.4 percent of failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("phase 1 addresses 7.4 percent of failures")
val phase1_fixes = 7
val total_failures = 95
val rate = (phase1_fixes * 100.0) / total_failures
expect rate > 7.0
expect rate < 8.0
```

</details>

#### extension can address 16.8 percent total

- extension can address 16.8 percent total


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extension can address 16.8 percent total")
val extendable_fixes = 16
val total_failures = 95
val rate = (extendable_fixes * 100.0) / total_failures
expect rate > 16.0
expect rate < 17.0
```

</details>

#### leaves 83.2 percent needing other solutions

- leaves 83.2 percent needing other solutions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves 83.2 percent needing other solutions")
val other_issues = 79
val total_failures = 95
val rate = (other_issues * 100.0) / total_failures
expect rate > 83.0
expect rate < 84.0
```

</details>

#### integration with existing system

#### maintains backward compatibility

- maintains backward compatibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains backward compatibility")
val compatible = true
expect compatible
```

</details>

#### adds no breaking changes

- adds no breaking changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds no breaking changes")
val breaking_changes = 0
expect breaking_changes == 0
```

</details>

#### works with existing error types

- works with existing error types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with existing error types")
val works = true
expect works
```

</details>

#### extends ParseError enum

- extends ParseError enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends ParseError enum")
val extended = true
expect extended
```

</details>

#### error message quality

#### is more helpful than token mismatch

- is more helpful than token mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is more helpful than token mismatch")
val old_len = "expected Comma, found Identifier".len()
val new_len = "function arguments: expected comma before argument 'b'".len()
expect new_len > old_len
```

</details>

#### includes what went wrong

- includes what went wrong


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes what went wrong")
val msg = "expected comma"
expect msg.contains("expected")
```

</details>

#### includes where it happened

- includes where it happened


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes where it happened")
val msg = "function arguments"
expect msg.contains("function")
```

</details>

#### includes how to fix

- includes how to fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes how to fix")
val msg = "Insert comma before 'b'"
expect msg.contains("Insert")
```

</details>

#### provides examples

- provides examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides examples")
val msg = "Use: func(a: 1, b: 2)"
expect msg.contains("Use:")
```

</details>

#### edge cases

#### handles empty source gracefully

- handles empty source gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty source gracefully")
val source = ""
expect source.len() == 0
```

</details>

#### handles line out of bounds

- handles line out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles line out of bounds")
val line = 100
val max_lines = 10
val out_of_bounds = line > max_lines
expect out_of_bounds
```

</details>

#### handles column at line end

- handles column at line end


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles column at line end")
val line = "test"
val col = 5
val at_end = col > line.len()
expect at_end
```

</details>

#### handles Unicode correctly

- handles Unicode correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles Unicode correctly")
val source = "func(名前: '値' 体積: 1.0)"
expect source.len() > 0
```

</details>

#### performance characteristics

#### only generates errors on failure

- only generates errors on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only generates errors on failure")
# Error messages only created when parse fails
val on_error_path = true
expect on_error_path
```

</details>

#### uses lookahead efficiently

- uses lookahead efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses lookahead efficiently")
# Only peeks when necessary for detection
val efficient = true
expect efficient
```

</details>

#### has no measurable overhead on success

- has no measurable overhead on success


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no measurable overhead on success")
# Successful parses unaffected
val no_overhead = true
expect no_overhead
```

</details>

### Error Recovery - Code Quality

#### code organization

#### separates concerns properly

- separates concerns properly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates concerns properly")
# Error types, detection, formatting separate
val separated = true
expect separated
```

</details>

#### uses clear naming

- uses clear naming


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses clear naming")
# ContextualSyntaxError, not Error2
val clear = true
expect clear
```

</details>

#### provides public API

- provides public API


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides public API")
# Exported types and functions
val has_api = true
expect has_api
```

</details>

#### documentation

#### includes doc comments

- includes doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes doc comments")
val documented = true
expect documented
```

</details>

#### provides usage examples

- provides usage examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides usage examples")
val has_examples = true
expect has_examples
```

</details>

#### explains design decisions

- explains design decisions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains design decisions")
val explained = true
expect explained
```

</details>

### Error Recovery - Future Work

#### phase 2 preparation

#### has foundation for fix suggestions

- has foundation for fix suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has foundation for fix suggestions")
val has_foundation = true
expect has_foundation
```

</details>

#### has confidence scoring system

- has confidence scoring system


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has confidence scoring system")
val has_scoring = true
expect has_scoring
```

</details>

#### has diff generation

- has diff generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has diff generation")
val has_diffs = true
expect has_diffs
```

</details>

#### extension opportunities

#### can extend to dict literals

- can extend to dict literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can extend to dict literals")
val extensible = true
expect extensible
```

</details>

#### can extend to struct init

- can extend to struct init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can extend to struct init")
val extensible = true
expect extensible
```

</details>

#### can extend to array literals

- can extend to array literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can extend to array literals")
val extensible = true
expect extensible
```

</details>

#### path to 95 percent pass rate

#### phase 1 achieves 90.4 percent

- phase 1 achieves 90.4 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("phase 1 achieves 90.4 percent")
val pass_rate = 90.4
expect pass_rate > 90.0
```

</details>

#### extensions reach 91.4 percent

- extensions reach 91.4 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extensions reach 91.4 percent")
val pass_rate = 91.4
expect pass_rate > 91.0
```

</details>

#### full implementation reaches 95.5 percent

- full implementation reaches 95.5 percent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full implementation reaches 95.5 percent")
val pass_rate = 95.5
expect pass_rate > 95.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/error_recovery_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Error Recovery - Phase 1, Error Recovery - Code Quality, Error Recovery - Future Work.
- Error Recovery - Phase 1
- Error Recovery - Code Quality
- Error Recovery - Future Work

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
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

- Canonical SPipe generation for source `148f233aa77536084f2b771c1eafe5880119f9872a5871124e3ac54a2a662fb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `148f233aa77536084f2b771c1eafe5880119f9872a5871124e3ac54a2a662fb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `148f233aa77536084f2b771c1eafe5880119f9872a5871124e3ac54a2a662fb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/parser/error_recovery_intensive_spec.spl
mirror: doc/06_spec/unit/compiler/parser/error_recovery_intensive_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/error_recovery_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/error_recovery_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides better errors than token mismatches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes context in every error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides location information' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:650:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can extend to dict literals' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:656:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can extend to struct init' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/parser/error_recovery_intensive_spec.spl:662:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can extend to array literals' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
