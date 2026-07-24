# LLM Caret Raw TUI Input Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 22 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 22 | 22 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/chat_tui_input_spec.spl`

## should decode CSI and SS3 arrows without leaking printable bytes

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 65])).to_equal(("up", ""))
expect(_decode_raw_bytes([27, 91, 66])).to_equal(("down", ""))
expect(_decode_raw_bytes([27, 91, 67])).to_equal(("right", ""))
expect(_decode_raw_bytes([27, 91, 68])).to_equal(("left", ""))
expect(_decode_raw_bytes([27, 79, 67])).to_equal(("right", ""))
```

</details>

## should decode direct and numeric home and end sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 72])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 70])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 91, 49, 126])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 52, 126])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 91, 55, 126])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 56, 126])).to_equal(("end", ""))
```

</details>

## should decode every supported SS3 navigation key

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 79, 65])).to_equal(("up", ""))
expect(_decode_raw_bytes([27, 79, 66])).to_equal(("down", ""))
expect(_decode_raw_bytes([27, 79, 67])).to_equal(("right", ""))
expect(_decode_raw_bytes([27, 79, 68])).to_equal(("left", ""))
expect(_decode_raw_bytes([27, 79, 70])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 79, 72])).to_equal(("home", ""))
```

</details>

## should swallow modified and unknown ANSI sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 49, 59, 53, 68])).to_equal(
    ("left", "")
)
expect(_decode_raw_bytes([27, 91, 51, 126])).to_equal(("", ""))
expect(_decode_raw_bytes([27, 120])).to_equal(("", ""))
```

</details>

## should preserve ordinary printable input after a completed sequence

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 67, 120])).to_equal(("right", "x"))
```

</details>

## should recover after abandoned and unknown escape sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes(
    [27, 91, 27, 91, 68, 120]
)).to_equal(("left", "x"))
expect(_decode_raw_bytes(
    [27, 91, 51, 126, 121]
)).to_equal(("", "y"))
```

</details>

## should apply decoded cursor keys without inserting escape bytes

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    97, 98, 99,
    27, 91, 68, 88,
    27, 91, 72, 62,
    27, 91, 70, 33
])
expect(edited).to_equal((">abXc!", 6))
```

</details>

## should insert valid two three and four byte code points

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xC2, 0xA2,
    0xED, 0x95, 0x9C,
    0xF0, 0x9F, 0x98, 0x80
])
expect(edited).to_equal(("¢한😀", 3))
```

</details>

## should accept the valid Unicode scalar boundary sequences

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xC2, 0x80,
    0xDF, 0xBF,
    0xE0, 0xA0, 0x80,
    0xED, 0x9F, 0xBF,
    0xEE, 0x80, 0x80,
    0xF0, 0x90, 0x80, 0x80,
    0xF4, 0x8F, 0xBF, 0xBF
])
val expected = (
    char_from_code(0x80) + char_from_code(0x7FF) +
    char_from_code(0x800) + char_from_code(0xD7FF) +
    char_from_code(0xE000) + char_from_code(0x10000) +
    char_from_code(0x10FFFF)
)
expect(edited).to_equal((expected, 7))
```

</details>

## should insert a decoded Unicode code point at the widget cursor

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    65, 66,
    27, 91, 68,
    0xED, 0x95, 0x9C
])
expect(edited).to_equal(("A한B", 2))
```

</details>

## should preserve ANSI navigation around decoded Unicode input

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xC2, 0xA2,
    0xF0, 0x9F, 0x98, 0x80,
    27, 91, 72, 62,
    27, 91, 70, 33
])
expect(edited).to_equal((">¢😀!", 4))
```

</details>

## should reject invalid leads and stray continuation bytes

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xC0, 0x80, 97,
    0xC1, 0xBF, 98,
    0xF5, 0x80, 0x80, 0x80, 99,
    0x80, 0xBF, 100
])
expect(edited).to_equal(("abcd", 4))
```

</details>

## should reject overlong surrogate and out of range sequences

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xE0, 0x80, 0xAF, 97,
    0xF0, 0x80, 0x80, 0xAF, 98,
    0xED, 0xA0, 0x80, 99,
    0xF4, 0x90, 0x80, 0x80, 100
])
expect(edited).to_equal(("abcd", 4))
```

</details>

## should fail closed when a sequence has an invalid continuation

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    0xE2, 65, 0x82, 0xAC, 66,
    0xF0, 0x9F, 67, 0x98, 0x80, 68
])
expect(edited).to_equal(("BD", 2))
```

</details>

## should retain incomplete sequences without inserting partial text

**Group:** UTF-8 raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_apply_raw_bytes([0xC2])).to_equal(("", 0))
expect(_apply_raw_bytes([0xE0, 0xA0])).to_equal(("", 0))
expect(_apply_raw_bytes([0xF0, 0x90, 0x80])).to_equal(("", 0))
```

</details>

## should submit the exact input on CR and LF in ordinary state

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
var state = make_raw_line_state(make_chat_tui("raw line").input)
state = step_raw_line_byte(state, 97).state
state = step_raw_line_byte(state, 98).state
val cr = step_raw_line_byte(state, 13)
val lf = step_raw_line_byte(state, 10)
expect(cr.action).to_equal(RAW_LINE_SUBMIT)
expect(cr.submitted).to_equal("ab")
expect(lf.action).to_equal(RAW_LINE_SUBMIT)
expect(lf.submitted).to_equal("ab")
```

</details>

## should delete before the cursor for DEL and BS

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
var state = make_raw_line_state(make_chat_tui("raw line").input)
state = step_raw_line_byte(state, 97).state
state = step_raw_line_byte(state, 98).state
state = step_raw_line_byte(state, 127).state
expect(state.input.value).to_equal("a")
state = step_raw_line_byte(state, 8).state
expect(state.input.value).to_equal("")
state = step_raw_line_byte(state, 8).state
expect(state.input.value).to_equal("")
```

</details>

## should emit paging actions only in ordinary state

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
val state = make_raw_line_state(make_chat_tui("raw line").input)
val older = step_raw_line_byte(state, 16)
val newer = step_raw_line_byte(state, 14)
expect(older.action).to_equal(RAW_LINE_PAGE_UP)
expect(newer.action).to_equal(RAW_LINE_PAGE_DOWN)
expect(older.state.input.value).to_equal("")
expect(newer.state.input.value).to_equal("")
```

</details>

## should exit on Ctrl-C Ctrl-D and EOF from every decoder state

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
val ordinary = make_raw_line_state(make_chat_tui("raw line").input)
val escape = step_raw_line_byte(ordinary, 27).state
val utf8 = step_raw_line_byte(ordinary, 0xE0).state
expect(step_raw_line_byte(ordinary, 3).action).to_equal(RAW_LINE_EXIT)
expect(step_raw_line_byte(escape, 4).action).to_equal(RAW_LINE_EXIT)
expect(step_raw_line_byte(utf8, -1).action).to_equal(RAW_LINE_EXIT)
```

</details>

## should give exit precedence over incomplete input sequences

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
val ordinary = make_raw_line_state(make_chat_tui("raw line").input)
val escape = step_raw_line_byte(ordinary, 27).state
val utf8 = step_raw_line_byte(ordinary, 0xF0).state
expect(step_raw_line_byte(escape, 3).action).to_equal(RAW_LINE_EXIT)
expect(step_raw_line_byte(utf8, 4).action).to_equal(RAW_LINE_EXIT)
```

</details>

## should swallow line controls inside an incomplete ANSI sequence

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
val ordinary = make_raw_line_state(make_chat_tui("raw line").input)
for b in [13, 127, 16, 14]:
    val escape = step_raw_line_byte(ordinary, 27).state
    val result = step_raw_line_byte(escape, b)
    expect(result.action).to_equal(RAW_LINE_CONTINUE)
    expect(result.submitted).to_equal("")
    expect(result.state.input.value).to_equal("")
```

</details>

## should preserve input while exiting or paging

**Group:** Raw-line control reduction

<details>
<summary>Executable SSpec</summary>

```simple
var state = make_raw_line_state(make_chat_tui("raw line").input)
state = step_raw_line_byte(state, 120).state
expect(step_raw_line_byte(state, 16).state.input.value).to_equal("x")
expect(step_raw_line_byte(state, 14).state.input.value).to_equal("x")
expect(step_raw_line_byte(state, 3).state.input.value).to_equal("x")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
