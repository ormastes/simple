# error_recovery_spec

> Enhanced error messages with context, suggestions, and help text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# error_recovery_spec

Enhanced error messages with context, suggestions, and help text.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/parser/error_recovery_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Enhanced error messages with context, suggestions, and help text.

    Goal: Replace cryptic token mismatch errors with actionable messages
    that explain WHAT went wrong, WHERE, and HOW to fix it.

## Scenarios

#### when creating contextual errors

#### creates error with all fields

- creates error with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error with all fields")
val err = ContextualSyntaxError(
    context="function arguments",
    message="expected comma before argument 'b'",
    span=Span(line=5, column=20),
    suggestion=Some("Insert comma before 'b'"),
    help=Some("Use: func(a: 1, b: 2)")
)

assert_equal(err.context, "function arguments")
assert_equal(err.message, "expected comma before argument 'b'")
assert_equal(err.span.line, 5)
assert_equal(err.span.column, 20)
err.suggestion.should_be_some()
err.help.should_be_some()
```

</details>

#### creates error without optional fields

- creates error without optional fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates error without optional fields")
val err = ContextualSyntaxError(
    context: "dict literal",
    message: "expected colon after key",
    span: Span(line: 10, column: 5),
    suggestion: None,
    help: None
)

err.suggestion.should_be_none()
err.help.should_be_none()
```

</details>

#### formats error message without color

- formats error message without color


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats error message without color")
val source = "fn test():\n    func(a: 1 b: 2)\n"
val err = ContextualSyntaxError(
    context: "function arguments",
    message: "expected comma before argument 'b'",
    span: Span(line: 2, column: 15),
    suggestion: Some("Insert comma before 'b'"),
    help: Some("Use: func(a: 1, b: 2)")
)

val formatted = err.format(source, use_color: false)

assert_contains(formatted, "error[E0013]")
assert_contains(formatted, "function arguments")
assert_contains(formatted, "expected comma before argument 'b'")
assert_contains(formatted, "line 2:15")
assert_contains(formatted, "func(a: 1 b: 2)")
assert_contains(formatted, "Suggestion: Insert comma before 'b'")
assert_contains(formatted, "Help: Use: func(a: 1, b: 2)")
```

</details>

#### formats error message with color

- formats error message with color


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats error message with color")
val source = "val x = {a: 1 b: 2}"
val err = ContextualSyntaxError(
    context: "dict literal",
    message: "expected comma between entries",
    span: Span(line: 1, column: 15),
    suggestion: Some("Insert comma after value"),
    help: None
)

val formatted = err.format(source, use_color: true)

assert_contains(formatted, "\x1b[1;31merror[E0013]:\x1b[0m")
assert_contains(formatted, "\x1b[1;36mSuggestion:\x1b[0m")
```

</details>

#### missing comma mistakes

#### provides message for missing comma in args

- provides message for missing comma in args


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing comma in args")
val mistake = CommonMistake.MissingCommaInArgs
val msg = mistake.message()

assert_contains(msg, "func(a: 1 b: 2)")
assert_contains(msg, "func(a: 1, b: 2)")
```

</details>

#### provides message for missing comma in dict

- provides message for missing comma in dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing comma in dict")
val mistake = CommonMistake.MissingCommaInDict
val msg = mistake.message()

assert_contains(msg, "{a: 1 b: 2}")
assert_contains(msg, "{a: 1, b: 2}")
```

</details>

#### provides message for missing comma in struct

- provides message for missing comma in struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing comma in struct")
val mistake = CommonMistake.MissingCommaInStruct
val msg = mistake.message()

assert_contains(msg, "Point(x: 1 y: 2)")
assert_contains(msg, "Point(x: 1, y: 2)")
```

</details>

#### provides suggestion for each mistake

- provides suggestion for each mistake


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides suggestion for each mistake")
CommonMistake.MissingCommaInArgs.suggestion()
   assert_equal( , "Insert comma between arguments")

CommonMistake.MissingCommaInDict.suggestion()
   assert_equal( , "Insert comma between dict entries")

CommonMistake.MissingCommaInStruct.suggestion()
   assert_equal( , "Insert comma between struct fields")
```

</details>

#### missing colon mistakes

#### provides message for missing colon before block

- provides message for missing colon before block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing colon before block")
val mistake = CommonMistake.MissingColonBeforeBlock
val msg = mistake.message()

assert_contains(msg, "fn foo()")
assert_contains(msg, "fn foo():")
```

</details>

#### provides message for missing colon in dict

- provides message for missing colon in dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing colon in dict")
val mistake = CommonMistake.MissingColonInDict
val msg = mistake.message()

assert_contains(msg, "{key value}")
assert_contains(msg, "{key: value}")
```

</details>

#### indentation mistakes

#### provides message for missing indent after colon

- provides message for missing indent after colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for missing indent after colon")
val mistake = CommonMistake.MissingIndentAfterColon
val msg = mistake.message()

assert_contains(msg, "fn foo():")
assert_contains(msg, "return 42")
assert_contains(msg, "    return 42")
```

</details>

#### provides message for wrong indent level

- provides message for wrong indent level


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for wrong indent level")
val mistake = CommonMistake.WrongIndentLevel
val msg = mistake.message()

assert_contains(msg, "Inconsistent indentation")
assert_contains(msg, "4 spaces or tabs")
```

</details>

#### language-specific mistakes

#### provides message for Python def

- provides message for Python def


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for Python def")
val mistake = CommonMistake.PythonDef
val msg = mistake.message()

assert_contains(msg, "def add(a, b)")
assert_contains(msg, "fn add(a, b)")
```

</details>

#### provides message for Python None

- provides message for Python None


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for Python None")
val mistake = CommonMistake.PythonNone
val msg = mistake.message()

assert_contains(msg, "return None")
assert_contains(msg, "return nil")
```

</details>

#### provides message for Rust let mut

- provides message for Rust let mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for Rust let mut")
val mistake = CommonMistake.RustLetMut
val msg = mistake.message()

assert_contains(msg, "let mut x = 5")
assert_contains(msg, "var x = 5")
```

</details>

#### provides message for Java new

- provides message for Java new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides message for Java new")
val mistake = CommonMistake.JavaNew
val msg = mistake.message()

assert_contains(msg, "new Point(1, 2)")
assert_contains(msg, "Point(x: 1, y: 2)")
```

</details>

#### detecting missing comma in function arguments

#### detects identifier followed by colon

- detects identifier followed by colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects identifier followed by colon")
val current = Token(
    kind: TokenKind.Identifier,
    lexeme: "volume",
    span: Span(line: 1, column: 20)
)
val next = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 26)
)

val is_missing = detect_missing_comma_in_args(current, next)
is_missing.should_be_true()
```

</details>

#### detects identifier followed by equals

- detects identifier followed by equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects identifier followed by equals")
val current = Token(
    kind: TokenKind.Identifier,
    lexeme: "name",
    span: Span(line: 1, column: 10)
)
val next = Token(
    kind: TokenKind.Assign,
    lexeme: "=",
    span: Span(line: 1, column: 15)
)

val is_missing = detect_missing_comma_in_args(current, next)
is_missing.should_be_true()
```

</details>

#### does not detect when not identifier

- does not detect when not identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect when not identifier")
val current = Token(
    kind: TokenKind.Comma,
    lexeme: ",",
    span: Span(line: 1, column: 10)
)
val next = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 11)
)

val is_missing = detect_missing_comma_in_args(current, next)
is_missing.should_be_false()
```

</details>

#### does not detect when next is not colon/equals

- does not detect when next is not colon/equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect when next is not colon/equals")
val current = Token(
    kind: TokenKind.Identifier,
    lexeme: "x",
    span: Span(line: 1, column: 5)
)
val next = Token(
    kind: TokenKind.RParen,
    lexeme: ")",
    span: Span(line: 1, column: 6)
)

val is_missing = detect_missing_comma_in_args(current, next)
is_missing.should_be_false()
```

</details>

#### detecting missing comma in dict

#### detects dict entry pattern

- detects dict entry pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects dict entry pattern")
val prev = Token(
    kind: TokenKind.Identifier,
    lexeme: "1",
    span: Span(line: 1, column: 8)
)
val current = Token(
    kind: TokenKind.Identifier,
    lexeme: "b",
    span: Span(line: 1, column: 10)
)
val next = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 11)
)

val is_missing = detect_missing_comma_in_dict(current, next, prev)
is_missing.should_be_true()
```

</details>

#### does not detect when prev is comma

- does not detect when prev is comma


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect when prev is comma")
val prev = Token(
    kind: TokenKind.Comma,
    lexeme: ",",
    span: Span(line: 1, column: 8)
)
val current = Token(
    kind: TokenKind.Identifier,
    lexeme: "b",
    span: Span(line: 1, column: 10)
)
val next = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 11)
)

val is_missing = detect_missing_comma_in_dict(current, next, prev)
is_missing.should_be_false()
```

</details>

#### detecting missing colon before block

#### detects newline after function signature

- detects newline after function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects newline after function signature")
val token = Token(
    kind: TokenKind.Newline,
    lexeme: "\n",
    span: Span(line: 1, column: 10)
)

val is_missing = detect_missing_colon_before_block(token)
is_missing.should_be_true()
```

</details>

#### detects indent after function signature

- detects indent after function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects indent after function signature")
val token = Token(
    kind: TokenKind.Indent,
    lexeme: "    ",
    span: Span(line: 2, column: 1)
)

val is_missing = detect_missing_colon_before_block(token)
is_missing.should_be_true()
```

</details>

#### does not detect other tokens

- does not detect other tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not detect other tokens")
val token = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 10)
)

val is_missing = detect_missing_colon_before_block(token)
is_missing.should_be_false()
```

</details>

#### creating fix suggestions

#### creates fix with high confidence

- creates fix with high confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates fix with high confidence")
val fix = FixSuggestion(
    description: "Insert missing comma",
    span: Span(line: 5, column: 15),
    replacement: ", ",
    confidence: Confidence.High
)

assert_equal(fix.description, "Insert missing comma")
assert_equal(fix.replacement, ", ")
assert_equal(fix.confidence, Confidence.High)
```

</details>

#### creates fix with medium confidence

- creates fix with medium confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates fix with medium confidence")
val fix = FixSuggestion(
    description: "Add indentation",
    span: Span(line: 10, column: 1),
    replacement: "    ",
    confidence: Confidence.Medium
)

assert_equal(fix.confidence, Confidence.Medium)
```

</details>

#### creates fix with low confidence

- creates fix with low confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates fix with low confidence")
val fix = FixSuggestion(
    description: "Possible fix",
    span: Span(line: 20, column: 5),
    replacement: ":",
    confidence: Confidence.Low
)

assert_equal(fix.confidence, Confidence.Low)
```

</details>

#### generating diffs

#### generates unified diff for insertion

- generates unified diff for insertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates unified diff for insertion")
val source = "func(a: 1 b: 2)"
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 1, column: 11),
    replacement: ", ",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)

assert_contains(diff, "--- before")
assert_contains(diff, "+++ after")
assert_contains(diff, "-func(a: 1 b: 2)")
assert_contains(diff, "+func(a: 1, b: 2)")
```

</details>

#### generates diff for multiple line source

- generates diff for multiple line source


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates diff for multiple line source")
val source = "fn test():\n    func(a: 1 b: 2)\n    return"
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 2, column: 15),
    replacement: ", ",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)

assert_contains(diff, "@@ -2,1 +2,1 @@")
assert_contains(diff, "-    func(a: 1 b: 2)")
assert_contains(diff, "+    func(a: 1, b: 2)")
```

</details>

#### managing collections of fixes

#### finds best fix from collection

- finds best fix from collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds best fix from collection")
val fixes = [
    FixSuggestion(
        description: "Fix 1",
        span: Span(line: 1, column: 1),
        replacement: ",",
        confidence: Confidence.Low
    ),
    FixSuggestion(
        description: "Fix 2",
        span: Span(line: 1, column: 1),
        replacement: ", ",
        confidence: Confidence.High
    ),
    FixSuggestion(
        description: "Fix 3",
        span: Span(line: 1, column: 1),
        replacement: " ,",
        confidence: Confidence.Medium
    )
]

val suggestions = FixSuggestions(
    error_message: "Missing comma",
    error_span: Span(line: 1, column: 10),
    fixes: fixes
)

val best = suggestions.best_fix()
best.should_be_some()
assert_equal(best.unwrap().confidence, Confidence.High)
assert_equal(best.unwrap().description, "Fix 2")
```

</details>

#### returns None when no fixes available

- returns None when no fixes available


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None when no fixes available")
val suggestions = FixSuggestions(
    error_message: "Error",
    error_span: Span(line: 1, column: 1),
    fixes: []
)

val best = suggestions.best_fix()
best.should_be_none()
```

</details>

#### building errors step by step

#### builds error with all fields

- builds error with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds error with all fields")
val err = ErrorBuilder()
    .context("function arguments")
    .message("expected comma before argument 'b'")
    .at_span(Span(line: 5, column: 20))
    .suggest("Insert comma before 'b'")
    .help_text("Use: func(a: 1, b: 2)")
    .build()

assert_equal(err.context, "function arguments")
assert_equal(err.message, "expected comma before argument 'b'")
assert_equal(err.span.line, 5)
assert_equal(err.span.column, 20)
err.suggestion.should_be_some()
err.help.should_be_some()
```

</details>

#### builds error with minimal fields

- builds error with minimal fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds error with minimal fields")
val err = ErrorBuilder()
    .context("dict literal")
    .message("expected colon")
    .at_span(Span(line: 10, column: 5))
    .build()

assert_equal(err.context, "dict literal")
assert_equal(err.message, "expected colon")
err.suggestion.should_be_none()
err.help.should_be_none()
```

</details>

#### allows method chaining in any order

- allows method chaining in any order


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows method chaining in any order")
val err = ErrorBuilder()
    .at_span(Span(line: 1, column: 1))
    .message("test message")
    .context("test context")
    .build()

assert_equal(err.context, "test context")
assert_equal(err.message, "test message")
```

</details>

#### handling missing comma in function call

#### detects error and provides full guidance

- detects error and provides full guidance


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects error and provides full guidance")
# Simulate parser state
val source = "AudioSource(name: 'test' volume: 1.0)"

val current_token = Token(
    kind: TokenKind.Identifier,
    lexeme: "volume",
    span: Span(line: 1, column: 26)
)

val next_token = Token(
    kind: TokenKind.Colon,
    lexeme: ":",
    span: Span(line: 1, column: 32)
)

# Detect mistake
val has_mistake = detect_missing_comma_in_args(current_token, next_token)
has_mistake.should_be_true()

# Create contextual error
val err = ErrorBuilder()
    .context("function arguments")
    .message("expected comma before argument 'volume'")
    .at_span(current_token.span)
    .suggest("Insert comma before 'volume'")
    .help_text("Use: AudioSource(name: 'test', volume: 1.0)")
    .build()

# Verify error message
val formatted = err.format(source, use_color: false)
assert_contains(formatted, "error[E0013]")
assert_contains(formatted, "function arguments")
assert_contains(formatted, "expected comma before argument 'volume'")

# Create fix suggestion
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 1, column: 25),
    replacement: ", ",
    confidence: Confidence.High
)

# Verify diff
val diff = fix.generate_diff(source)
assert_contains(diff, "AudioSource(name: 'test' volume: 1.0)")
assert_contains(diff, "AudioSource(name: 'test', volume: 1.0)")
```

</details>

#### handling missing comma in dict literal

#### provides complete error recovery workflow

- provides complete error recovery workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides complete error recovery workflow")
val source = "{key1: 'value1' key2: 'value2'}"

# Detect pattern
val prev = Token(kind: TokenKind.Identifier, lexeme: "'value1'", span: Span(line: 1, column: 15))
val current = Token(kind: TokenKind.Identifier, lexeme: "key2", span: Span(line: 1, column: 17))
val next = Token(kind: TokenKind.Colon, lexeme: ":", span: Span(line: 1, column: 21))

val has_mistake = detect_missing_comma_in_dict(current, next, prev)
has_mistake.should_be_true()

# Build error
val err = ErrorBuilder()
    .context("dict literal")
    .message("expected comma between dict entries")
    .at_span(current.span)
    .suggest("Insert comma after the value")
    .help_text("Dict entries must be separated by commas: {a: 1, b: 2}")
    .build()

assert_equal(err.context, "dict literal")
err.suggestion.should_be_some()
```

</details>

#### handling missing colon before block

#### provides complete error recovery workflow

- provides complete error recovery workflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides complete error recovery workflow")
val source = "fn test()\n    return 42"

# Detect pattern
val token = Token(kind: TokenKind.Newline, lexeme: "\n", span: Span(line: 1, column: 10))

val has_mistake = detect_missing_colon_before_block(token)
has_mistake.should_be_true()

# Build error
val err = ErrorBuilder()
    .context("function definition")
    .message("expected colon before function body")
    .at_span(token.span)
    .suggest("Insert ':' at end of line")
    .help_text("Function definitions require a colon: fn name():")
    .build()

# Verify
val formatted = err.format(source, use_color: false)
assert_contains(formatted, "function definition")
assert_contains(formatted, "expected colon before function body")
```

</details>

#### handling invalid spans

#### handles line out of bounds gracefully

- handles line out of bounds gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles line out of bounds gracefully")
val source = "short"
val fix = FixSuggestion(
    description: "Fix",
    span: Span(line: 100, column: 1),
    replacement: ",",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)
assert_contains(diff, "Error: line out of bounds")
```

</details>

#### handles column at line boundary

- handles column at line boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles column at line boundary")
val source = "test"
val fix = FixSuggestion(
    description: "Fix",
    span: Span(line: 1, column: 5),
    replacement: ",",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)
assert_contains(diff, "+test,")
```

</details>

#### handling empty inputs

#### formats error for empty source

- formats error for empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats error for empty source")
val err = ContextualSyntaxError(
    context: "test",
    message: "test error",
    span: Span(line: 1, column: 1),
    suggestion: None,
    help: None
)

val formatted = err.format("", use_color: false)
assert_contains(formatted, "error[E0013]")
```

</details>

#### handles empty fixes collection

- handles empty fixes collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty fixes collection")
val suggestions = FixSuggestions(
    error_message: "Error",
    error_span: Span(line: 1, column: 1),
    fixes: []
)

suggestions.best_fix().should_be_none()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
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

- Canonical SPipe generation for source `5c73d64c08d61396eb36203001071e8dfcd068eea1b21f974678aff8b6bdc53a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c73d64c08d61396eb36203001071e8dfcd068eea1b21f974678aff8b6bdc53a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c73d64c08d61396eb36203001071e8dfcd068eea1b21f974678aff8b6bdc53a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/lib/std/parser/error_recovery_spec.spl
mirror: doc/06_spec/unit/lib/std/parser/error_recovery_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/parser/error_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/parser/error_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/parser/error_recovery_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/std/parser/error_recovery_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates error with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/parser/error_recovery_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates error without optional fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/parser/error_recovery_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats error message without color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
