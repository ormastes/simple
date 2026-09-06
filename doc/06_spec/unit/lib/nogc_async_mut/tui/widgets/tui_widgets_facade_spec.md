# Tui Widgets Facade Specification

> Tests covering nogc_async_mut tui widgets facade, input widget cursor arithmetic is codepoint based.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Widgets Facade Specification

## Scenarios

### nogc_async_mut tui widgets facade

#### re-exports text, box, list, and input widget behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports text, box, list, and input widget behavior
   - Expected: text_render(text_widget, area).len() equals `3`
   - Expected: box_inner_area(make_rect(0, 0, 10, 4)).width equals `8`
   - Expected: list_selected_item(selected) equals `b`
   - Expected: input.value equals `xab`
   - Expected: input.value equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports text, box, list, and input widget behavior")
val style = tui_default_style()
val area = make_rect(0, 0, 10, 3)
val text_widget = make_text_widget_aligned("hi", style, ALIGN_CENTER)
expect(text_render(text_widget, area).len()).to_equal(3)
val box_widget = make_box_widget("T", style)
expect(box_inner_area(make_rect(0, 0, 10, 4)).width).to_equal(8)
val selected = list_select(make_list_widget(["a", "b"], style, style), 1)
expect(list_selected_item(selected)).to_equal("b")
var input = make_input_widget_with_value("> ", "ab", style)
input = input_move_home(input)
input = input_insert_char(input, "x")
expect(input.value).to_equal("xab")
input = input_delete_back(input)
expect(input.value).to_equal("ab")
```

</details>

### input widget cursor arithmetic is codepoint based

#### inserts two, three and four byte code points advancing one cell each

- inserts two, three and four byte code points advancing one cell each
   - Expected: (input.value, input.cursor_pos) equals `("¢한😀", 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts two, three and four byte code points advancing one cell each")
var input = make_input_widget("", tui_default_style())
input = input_insert_char(input, "¢")
input = input_insert_char(input, "한")
input = input_insert_char(input, "😀")
expect((input.value, input.cursor_pos)).to_equal(("¢한😀", 3))
```

</details>

#### deletes backward over a four byte emoji as one unit

- deletes backward over a four byte emoji as one unit
   - Expected: input.cursor_pos equals `3`
   - Expected: (input.value, input.cursor_pos) equals `("ab", 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes backward over a four byte emoji as one unit")
var input = make_input_widget_with_value("", "a😀b", tui_default_style())
expect(input.cursor_pos).to_equal(3)
input = input_move_left(input)
input = input_delete_back(input)
expect((input.value, input.cursor_pos)).to_equal(("ab", 1))
```

</details>

#### moves left across a three byte hangul one code point at a time

- moves left across a three byte hangul one code point at a time
   - Expected: input.cursor_pos equals `2`
   - Expected: input.cursor_pos equals `1`
   - Expected: input.cursor_pos equals `0`
   - Expected: input.cursor_pos equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves left across a three byte hangul one code point at a time")
var input = make_input_widget_with_value("", "한글", tui_default_style())
expect(input.cursor_pos).to_equal(2)
input = input_move_left(input)
expect(input.cursor_pos).to_equal(1)
input = input_move_left(input)
expect(input.cursor_pos).to_equal(0)
input = input_move_left(input)
expect(input.cursor_pos).to_equal(0)
```

</details>

#### inserts in the middle of multibyte text without splitting a sequence

- inserts in the middle of multibyte text without splitting a sequence
   - Expected: (input.value, input.cursor_pos) equals `("¢한😀", 2)`
   - Expected: (input.value, input.cursor_pos) equals `("¢한", 2)`
   - Expected: input.cursor_pos equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts in the middle of multibyte text without splitting a sequence")
var input = make_input_widget_with_value("", "¢😀", tui_default_style())
input = input_move_home(input)
input = input_move_right(input)
input = input_insert_char(input, "한")
expect((input.value, input.cursor_pos)).to_equal(("¢한😀", 2))
input = input_delete_forward(input)
expect((input.value, input.cursor_pos)).to_equal(("¢한", 2))
input = input_move_end(input)
expect(input.cursor_pos).to_equal(2)
```

</details>

#### keeps ASCII editing unchanged

- keeps ASCII editing unchanged
   - Expected: input.cursor_pos equals `2`
   - Expected: (input.value, input.cursor_pos) equals `("abc", 3)`
   - Expected: (input.value, input.cursor_pos) equals `("bc", 0)`
   - Expected: (input.value, input.cursor_pos) equals `("b", 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ASCII editing unchanged")
var input = make_input_widget_with_value("", "ab", tui_default_style())
expect(input.cursor_pos).to_equal(2)
input = input_insert_char(input, "c")
expect((input.value, input.cursor_pos)).to_equal(("abc", 3))
input = input_move_home(input)
input = input_delete_forward(input)
expect((input.value, input.cursor_pos)).to_equal(("bc", 0))
input = input_move_end(input)
input = input_delete_back(input)
expect((input.value, input.cursor_pos)).to_equal(("b", 1))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut tui widgets facade, input widget cursor arithmetic is codepoint based.
- nogc_async_mut tui widgets facade
- input widget cursor arithmetic is codepoint based

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `0d4f88525cdfaca1e4cdcd9e038f07cceea7d2cd393fcb31b934e12f099a3c37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d4f88525cdfaca1e4cdcd9e038f07cceea7d2cd393fcb31b934e12f099a3c37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d4f88525cdfaca1e4cdcd9e038f07cceea7d2cd393fcb31b934e12f099a3c37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports text, box, list, and input widget behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts two, three and four byte code points advancing one cell each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deletes backward over a four byte emoji as one unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
