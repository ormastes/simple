# Widget Eval Specification

> <details>

<!-- sdn-diagram:id=widget_eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_eval_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Eval Specification

## Scenarios

### DslArg

#### constructs positional arg with empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = DslArg(name: "", value: "Hello")
expect(arg.name).to_equal("")
expect(arg.value).to_equal("Hello")
```

</details>

#### constructs named arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = DslArg(name: "title", value: "Dashboard")
expect(arg.name).to_equal("title")
expect(arg.value).to_equal("Dashboard")
```

</details>

### DslLine

#### constructs container line

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = DslLine(
    indent: 0,
    widget_type: "column",
    args: [],
    is_container: true
)
expect(line.widget_type).to_equal("column")
expect(line.is_container).to_equal(true)
```

</details>

#### constructs leaf line

1. args: [DslArg
   - Expected: line.widget_type equals `text`
   - Expected: line.is_container is false
   - Expected: line.indent equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = DslLine(
    indent: 4,
    widget_type: "text",
    args: [DslArg(name: "", value: "Hello")],
    is_container: false
)
expect(line.widget_type).to_equal("text")
expect(line.is_container).to_equal(false)
expect(line.indent).to_equal(4)
```

</details>

### WidgetDslEvaluator

#### starts with _id_counter at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eval = WidgetDslEvaluator.new()
expect(eval._id_counter).to_equal(0)
```

</details>

### Widget DSL — text widget

#### parses text(\

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session)  # session is not nil`
3. Err
   - Expected: e equals `"")  # should not error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "text(\"Hello\")"
val result = eval.evaluate(dsl)
# Should succeed
match result:
    Ok(session):
        expect(session).to_equal(session)  # session is not nil
    Err(e):
        expect(e).to_equal("")  # should not error
```

</details>

#### parses simple label

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "label(\"CPU:\")"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

### Widget DSL — column layout

#### parses column with text children

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "column:\n    text(\"A\")\n    text(\"B\")"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

#### parses nested column and row

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "column:\n    row:\n        text(\"Left\")\n        text(\"Right\")"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

### Widget DSL — named arguments

#### parses progress with value and max

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "progress(value: 75, max: 100)"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

#### parses panel with title

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "panel(title: \"Dashboard\"):\n    text(\"content\")"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

#### parses button with label and action

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "button(\"OK\", action: \"submit\")"
val result = eval.evaluate(dsl)
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

### Widget DSL — error handling

#### returns error for empty DSL input

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: "should have errored" equals ``
3. Err
   - Expected: e equals `Empty DSL input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("")
match result:
    Ok(_):
        expect("should have errored").to_equal("")
    Err(e):
        expect(e).to_equal("Empty DSL input")
```

</details>

#### returns error for whitespace-only input

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: "should have errored" equals ``
3. Err
   - Expected: e equals `Empty DSL input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("   \n   \n   ")
match result:
    Ok(_):
        expect("should have errored").to_equal("")
    Err(e):
        expect(e).to_equal("Empty DSL input")
```

</details>

#### returns error for comment-only input

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: "should have errored" equals ``
3. Err
   - Expected: e equals `Empty DSL input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("# just a comment")
match result:
    Ok(_):
        expect("should have errored").to_equal("")
    Err(e):
        expect(e).to_equal("Empty DSL input")
```

</details>

#### handles unknown widget type gracefully

1. var eval = WidgetDslEvaluator new
2. Ok
   - Expected: session equals `session`
3. Err
   - Expected: e equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val dsl = "foobar(\"test\")"
val result = eval.evaluate(dsl)
# Unknown types create a generic panel, so should succeed
match result:
    Ok(session):
        expect(session).to_equal(session)
    Err(e):
        expect(e).to_equal("")
```

</details>

### Widget DSL — _parse_dsl_lines

#### parses single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("text(\"Hello\")")
expect(lines.len()).to_equal(1)
expect(lines[0].widget_type).to_equal("text")
```

</details>

#### skips blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("\n\ntext(\"Hello\")\n\n")
expect(lines.len()).to_equal(1)
```

</details>

#### skips comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("# comment\ntext(\"Hello\")")
expect(lines.len()).to_equal(1)
expect(lines[0].widget_type).to_equal("text")
```

</details>

#### measures indentation correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("    text(\"indented\")")
expect(lines[0].indent).to_equal(4)
```

</details>

#### detects container lines ending with colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("column:")
expect(lines[0].is_container).to_equal(true)
```

</details>

#### detects leaf lines without colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _parse_dsl_lines("text(\"leaf\")")
expect(lines[0].is_container).to_equal(false)
```

</details>

#### parses multiple lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dsl = "column:\n    text(\"A\")\n    text(\"B\")"
val lines = _parse_dsl_lines(dsl)
expect(lines.len()).to_equal(3)
expect(lines[0].widget_type).to_equal("column")
expect(lines[1].widget_type).to_equal("text")
expect(lines[2].widget_type).to_equal("text")
```

</details>

### Widget DSL — argument parsing

#### _get_arg returns named arg by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [DslArg(name: "title", value: "Hello")]
val result = _get_arg(args, "title", 0)
expect(result).to_equal("Hello")
```

</details>

#### _get_arg returns positional arg by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [DslArg(name: "", value: "First")]
val result = _get_arg(args, "unused", 0)
expect(result).to_equal("First")
```

</details>

#### _get_arg returns empty for missing arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args: [DslArg] = []
val result = _get_arg(args, "missing", 0)
expect(result).to_equal("")
```

</details>

#### _get_named_arg returns named value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [DslArg(name: "key", value: "value")]
val result = _get_named_arg(args, "key")
expect(result).to_equal("value")
```

</details>

#### _get_named_arg returns empty for missing name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = [DslArg(name: "other", value: "value")]
val result = _get_named_arg(args, "missing")
expect(result).to_equal("")
```

</details>

#### _strip_quotes removes double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _strip_quotes("\"hello\"")
expect(result).to_equal("hello")
```

</details>

#### _strip_quotes removes single quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _strip_quotes("'hello'")
expect(result).to_equal("hello")
```

</details>

#### _strip_quotes leaves unquoted strings unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _strip_quotes("hello")
expect(result).to_equal("hello")
```

</details>

#### _count_indent counts leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _count_indent("    text")
expect(result).to_equal(4)
```

</details>

#### _count_indent returns 0 for no indent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _count_indent("text")
expect(result).to_equal(0)
```

</details>

#### _count_indent returns 8 for double indent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _count_indent("        text")
expect(result).to_equal(8)
```

</details>

### Widget DSL — all widget types

#### parses divider

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("divider")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses checkbox

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("checkbox(\"Enable\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses statusbar

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("statusbar(\"Ready\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses input

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("input(\"Type here...\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses heading

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("heading(\"Title\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses image with src and alt

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("image(src: \"/icon.png\", alt: \"icon\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses list widget

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("list:\n    text(\"item1\")\n    text(\"item2\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

#### parses table widget

1. var eval = WidgetDslEvaluator new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval = WidgetDslEvaluator.new()
val result = eval.evaluate("table(headers: \"PID,Name\")")
match result:
    Ok(session): expect(session).to_equal(session)
    Err(e): expect(e).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/llm/widget_eval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DslArg
- DslLine
- WidgetDslEvaluator
- Widget DSL — text widget
- Widget DSL — column layout
- Widget DSL — named arguments
- Widget DSL — error handling
- Widget DSL — _parse_dsl_lines
- Widget DSL — argument parsing
- Widget DSL — all widget types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
