# TUI input widget: multibyte insert advances cursor by BYTES and corrupts the value — 2026-08-25

Status: OPEN (P2) — defect in `src/lib/nogc_sync_mut/tui/widgets/input.spl`
(std), surfaced by the llm_caret decoder spec. Not fixed here (outside
`src/app/llm_caret/**`); spec stays RED.

## Symptom

`test/01_unit/app/llm_caret/chat_tui_input_spec.spl` —
`Results: 22 total, 18 passed, 4 failed` (fresh seed from origin/main
`684fadabcae`):

```
✗ should insert valid two three and four byte code points
    expected (���, 9) to equal (¢한😀, 3)
✗ should accept the valid Unicode scalar boundary sequences
    expected (�������, 21) to equal (�������, 7)
✗ should insert a decoded Unicode code point at the widget cursor
    expected (A�B, 4) to equal (A한B, 2)
✗ should preserve ANSI navigation around decoded Unicode input
    expected (>��!, 8) to equal (>¢😀!, 4)
```

## Root cause

The byte-at-a-time decoder in `src/app/llm_caret/tui_input.spl:101-165` is
correct: it emits one completed code point per sequence
(`_utf8_emit_or_reject`). `apply_raw_key_decode` (`tui_input.spl:167-178`)
then calls `input_insert_char(input, char_from_code(cp))`, and
`src/lib/nogc_sync_mut/tui/widgets/input.spl:98-106` does

```
val before = widget.value.substring(0, widget.cursor_pos)
val after  = widget.value.substring(widget.cursor_pos, len(widget.value))
...
cursor_pos: widget.cursor_pos + len(ch),
```

`len()` is a BYTE count by contract
(`test/01_unit/lib/common/text_byte_len_vs_codepoint_index_spec.spl`:
"`text.len()` / `text.length()` are BYTE counts, while `char_at(i)` … are
CODEPOINT-indexed"), so the cursor advances 2/3/4 per code point (hence 9 for
three code points) while `substring` slices by code point, and the next insert
splits the buffer mid-sequence — the replacement characters above. Same defect
class as `doc/08_tracking/bug/text_byte_len_vs_codepoint_index_family_2026-08-06.md`.

Minimal repro on the fresh seed: `char_from_code(0xA2)` equals `"¢"` but
`.len()` is 2; `"¢".len()` is 2.

## Unblock condition

`input_insert_char` (and the sibling delete/move helpers in the same widget)
must advance/measure in code points (`+ 1` per inserted code point, or a
codepoint-length helper), keeping `substring` semantics. Re-verify with
`bin/simple test test/01_unit/app/llm_caret/chat_tui_input_spec.spl`.
