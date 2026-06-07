# error_recovery_spec

> Enhanced error messages with context, suggestions, and help text.

<!-- sdn-diagram:id=error_recovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_recovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_recovery_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_recovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/lib/std/parser/error_recovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Enhanced error messages with context, suggestions, and help text.

    Goal: Replace cryptic token mismatch errors with actionable messages
    that explain WHAT went wrong, WHERE, and HOW to fix it.

## Scenarios

#### when creating contextual errors

#### creates error with all fields

1. span=Span
2. suggestion=Some
3. help=Some
4. err context should equal
5. err message should equal
6. err span line should equal
7. err span column should equal
8. err suggestion should be some
9. err help should be some


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ContextualSyntaxError(
    context="function arguments",
    message="expected comma before argument 'b'",
    span=Span(line=5, column=20),
    suggestion=Some("Insert comma before 'b'"),
    help=Some("Use: func(a: 1, b: 2)")
)

err.context.should_equal("function arguments")
err.message.should_equal("expected comma before argument 'b'")
err.span.line.should_equal(5)
err.span.column.should_equal(20)
err.suggestion.should_be_some()
err.help.should_be_some()
```

</details>

#### creates error without optional fields

1. span: Span
2. err suggestion should be none
3. err help should be none


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. suggestion: Some
3. help: Some
4. formatted should contain
5. formatted should contain
6. formatted should contain
7. formatted should contain
8. formatted should contain
9. formatted should contain
10. formatted should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn test():\n    func(a: 1 b: 2)\n"
val err = ContextualSyntaxError(
    context: "function arguments",
    message: "expected comma before argument 'b'",
    span: Span(line: 2, column: 15),
    suggestion: Some("Insert comma before 'b'"),
    help: Some("Use: func(a: 1, b: 2)")
)

val formatted = err.format(source, use_color: false)

formatted.should_contain("error[E0013]")
formatted.should_contain("function arguments")
formatted.should_contain("expected comma before argument 'b'")
formatted.should_contain("line 2:15")
formatted.should_contain("func(a: 1 b: 2)")
formatted.should_contain("Suggestion: Insert comma before 'b'")
formatted.should_contain("Help: Use: func(a: 1, b: 2)")
```

</details>

#### formats error message with color

1. span: Span
2. suggestion: Some
3. formatted should contain
4. formatted should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = {a: 1 b: 2}"
val err = ContextualSyntaxError(
    context: "dict literal",
    message: "expected comma between entries",
    span: Span(line: 1, column: 15),
    suggestion: Some("Insert comma after value"),
    help: None
)

val formatted = err.format(source, use_color: true)

formatted.should_contain("\x1b[1;31merror[E0013]:\x1b[0m")
formatted.should_contain("\x1b[1;36mSuggestion:\x1b[0m")
```

</details>

#### missing comma mistakes

#### provides message for missing comma in args

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingCommaInArgs
val msg = mistake.message()

msg.should_contain("func(a: 1 b: 2)")
msg.should_contain("func(a: 1, b: 2)")
```

</details>

#### provides message for missing comma in dict

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingCommaInDict
val msg = mistake.message()

msg.should_contain("{a: 1 b: 2}")
msg.should_contain("{a: 1, b: 2}")
```

</details>

#### provides message for missing comma in struct

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingCommaInStruct
val msg = mistake.message()

msg.should_contain("Point(x: 1 y: 2)")
msg.should_contain("Point(x: 1, y: 2)")
```

</details>

#### provides suggestion for each mistake

1. CommonMistake MissingCommaInArgs suggestion
2.  should equal
3. CommonMistake MissingCommaInDict suggestion
4.  should equal
5. CommonMistake MissingCommaInStruct suggestion
6.  should equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
CommonMistake.MissingCommaInArgs.suggestion()
    .should_equal("Insert comma between arguments")

CommonMistake.MissingCommaInDict.suggestion()
    .should_equal("Insert comma between dict entries")

CommonMistake.MissingCommaInStruct.suggestion()
    .should_equal("Insert comma between struct fields")
```

</details>

#### missing colon mistakes

#### provides message for missing colon before block

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingColonBeforeBlock
val msg = mistake.message()

msg.should_contain("fn foo()")
msg.should_contain("fn foo():")
```

</details>

#### provides message for missing colon in dict

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingColonInDict
val msg = mistake.message()

msg.should_contain("{key value}")
msg.should_contain("{key: value}")
```

</details>

#### indentation mistakes

#### provides message for missing indent after colon

1. msg should contain
2. msg should contain
3. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.MissingIndentAfterColon
val msg = mistake.message()

msg.should_contain("fn foo():")
msg.should_contain("return 42")
msg.should_contain("    return 42")
```

</details>

#### provides message for wrong indent level

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.WrongIndentLevel
val msg = mistake.message()

msg.should_contain("Inconsistent indentation")
msg.should_contain("4 spaces or tabs")
```

</details>

#### language-specific mistakes

#### provides message for Python def

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.PythonDef
val msg = mistake.message()

msg.should_contain("def add(a, b)")
msg.should_contain("fn add(a, b)")
```

</details>

#### provides message for Python None

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.PythonNone
val msg = mistake.message()

msg.should_contain("return None")
msg.should_contain("return nil")
```

</details>

#### provides message for Rust let mut

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.RustLetMut
val msg = mistake.message()

msg.should_contain("let mut x = 5")
msg.should_contain("var x = 5")
```

</details>

#### provides message for Java new

1. msg should contain
2. msg should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mistake = CommonMistake.JavaNew
val msg = mistake.message()

msg.should_contain("new Point(1, 2)")
msg.should_contain("Point(x: 1, y: 2)")
```

</details>

#### detecting missing comma in function arguments

#### detects identifier followed by colon

1. span: Span
2. span: Span
3. is missing should be true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. span: Span
3. is missing should be true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. span: Span
3. is missing should be false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. span: Span
3. is missing should be false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. span: Span
3. span: Span
4. is missing should be true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. span: Span
3. span: Span
4. is missing should be false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. is missing should be true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. is missing should be true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. is missing should be false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. span: Span
2. fix description should equal
3. fix replacement should equal
4. fix confidence should equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = FixSuggestion(
    description: "Insert missing comma",
    span: Span(line: 5, column: 15),
    replacement: ", ",
    confidence: Confidence.High
)

fix.description.should_equal("Insert missing comma")
fix.replacement.should_equal(", ")
fix.confidence.should_equal(Confidence.High)
```

</details>

#### creates fix with medium confidence

1. span: Span
2. fix confidence should equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = FixSuggestion(
    description: "Add indentation",
    span: Span(line: 10, column: 1),
    replacement: "    ",
    confidence: Confidence.Medium
)

fix.confidence.should_equal(Confidence.Medium)
```

</details>

#### creates fix with low confidence

1. span: Span
2. fix confidence should equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = FixSuggestion(
    description: "Possible fix",
    span: Span(line: 20, column: 5),
    replacement: ":",
    confidence: Confidence.Low
)

fix.confidence.should_equal(Confidence.Low)
```

</details>

#### generating diffs

#### generates unified diff for insertion

1. span: Span
2. diff should contain
3. diff should contain
4. diff should contain
5. diff should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "func(a: 1 b: 2)"
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 1, column: 11),
    replacement: ", ",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)

diff.should_contain("--- before")
diff.should_contain("+++ after")
diff.should_contain("-func(a: 1 b: 2)")
diff.should_contain("+func(a: 1, b: 2)")
```

</details>

#### generates diff for multiple line source

1. span: Span
2. diff should contain
3. diff should contain
4. diff should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn test():\n    func(a: 1 b: 2)\n    return"
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 2, column: 15),
    replacement: ", ",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)

diff.should_contain("@@ -2,1 +2,1 @@")
diff.should_contain("-    func(a: 1 b: 2)")
diff.should_contain("+    func(a: 1, b: 2)")
```

</details>

#### managing collections of fixes

#### finds best fix from collection

1. span: Span
2. span: Span
3. span: Span
4. error span: Span
5. best should be some
6. best unwrap
7. best unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
best.unwrap().confidence.should_equal(Confidence.High)
best.unwrap().description.should_equal("Fix 2")
```

</details>

#### returns None when no fixes available

1. error span: Span
2. best should be none


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  context
2.  message
3.  at span
4.  suggest
5.  help text
6.  build
7. err context should equal
8. err message should equal
9. err span line should equal
10. err span column should equal
11. err suggestion should be some
12. err help should be some


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ErrorBuilder()
    .context("function arguments")
    .message("expected comma before argument 'b'")
    .at_span(Span(line: 5, column: 20))
    .suggest("Insert comma before 'b'")
    .help_text("Use: func(a: 1, b: 2)")
    .build()

err.context.should_equal("function arguments")
err.message.should_equal("expected comma before argument 'b'")
err.span.line.should_equal(5)
err.span.column.should_equal(20)
err.suggestion.should_be_some()
err.help.should_be_some()
```

</details>

#### builds error with minimal fields

1.  context
2.  message
3.  at span
4.  build
5. err context should equal
6. err message should equal
7. err suggestion should be none
8. err help should be none


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ErrorBuilder()
    .context("dict literal")
    .message("expected colon")
    .at_span(Span(line: 10, column: 5))
    .build()

err.context.should_equal("dict literal")
err.message.should_equal("expected colon")
err.suggestion.should_be_none()
err.help.should_be_none()
```

</details>

#### allows method chaining in any order

1.  at span
2.  message
3.  context
4.  build
5. err context should equal
6. err message should equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ErrorBuilder()
    .at_span(Span(line: 1, column: 1))
    .message("test message")
    .context("test context")
    .build()

err.context.should_equal("test context")
err.message.should_equal("test message")
```

</details>

#### handling missing comma in function call

#### detects error and provides full guidance

1. span: Span
2. span: Span
3. has mistake should be true
4.  context
5.  message
6.  at span
7.  suggest
8.  help text
9.  build
10. formatted should contain
11. formatted should contain
12. formatted should contain
13. span: Span
14. diff should contain
15. diff should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
formatted.should_contain("error[E0013]")
formatted.should_contain("function arguments")
formatted.should_contain("expected comma before argument 'volume'")

# Create fix suggestion
val fix = FixSuggestion(
    description: "Insert comma",
    span: Span(line: 1, column: 25),
    replacement: ", ",
    confidence: Confidence.High
)

# Verify diff
val diff = fix.generate_diff(source)
diff.should_contain("AudioSource(name: 'test' volume: 1.0)")
diff.should_contain("AudioSource(name: 'test', volume: 1.0)")
```

</details>

#### handling missing comma in dict literal

#### provides complete error recovery workflow

1. has mistake should be true
2.  context
3.  message
4.  at span
5.  suggest
6.  help text
7.  build
8. err context should equal
9. err suggestion should be some


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

err.context.should_equal("dict literal")
err.suggestion.should_be_some()
```

</details>

#### handling missing colon before block

#### provides complete error recovery workflow

1. has mistake should be true
2.  context
3.  message
4.  at span
5.  suggest
6.  help text
7.  build
8. formatted should contain
9. formatted should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
formatted.should_contain("function definition")
formatted.should_contain("expected colon before function body")
```

</details>

#### handling invalid spans

#### handles line out of bounds gracefully

1. span: Span
2. diff should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "short"
val fix = FixSuggestion(
    description: "Fix",
    span: Span(line: 100, column: 1),
    replacement: ",",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)
diff.should_contain("Error: line out of bounds")
```

</details>

#### handles column at line boundary

1. span: Span
2. diff should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "test"
val fix = FixSuggestion(
    description: "Fix",
    span: Span(line: 1, column: 5),
    replacement: ",",
    confidence: Confidence.High
)

val diff = fix.generate_diff(source)
diff.should_contain("+test,")
```

</details>

#### handling empty inputs

#### formats error for empty source

1. span: Span
2. formatted should contain


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = ContextualSyntaxError(
    context: "test",
    message: "test error",
    span: Span(line: 1, column: 1),
    suggestion: None,
    help: None
)

val formatted = err.format("", use_color: false)
formatted.should_contain("error[E0013]")
```

</details>

#### handles empty fixes collection

1. error span: Span
2. suggestions best fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
