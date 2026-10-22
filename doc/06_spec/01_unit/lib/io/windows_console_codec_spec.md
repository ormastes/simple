# Windows console key and mode codec

Source: `test/01_unit/lib/io/windows_console_codec_spec.spl`.
Authored manual; executable results remain pending.

| Scenario | Required value |
|---|---|
| Raw input flags | Processed/line/echo/QuickEdit/mouse/VT-input cleared, unrelated bits retained |
| VT output flags | Existing flags retained and processed/VT/deferred wrap enabled |
| Ctrl-C | Byte 3, including zero UnicodeChar |
| Arrow/repeat | Complete ESC[A plus compact repeat counter 65535 |
| Modifier/keyup | No emitted input and no lost surrogate carry |
| Split surrogate | Two OS batches produce 😀 |
| Repeated surrogate | Counts combine without expanding allocations |
| Unmatched surrogate | Replacement followed by ordinary input |
| AltGr | Printable @ preserved |
| Alt and Shift-Tab | One Alt prefix and complete reverse-tab sequence |
| Other controls | Ctrl-Space NUL, Backspace DEL |
| UTF16 width | ASCII/Korean/emoji/NUL count five code units |

These value tests do not qualify Win64 linkage, actual console event delivery,
mode restoration or system clipboard ownership. Run the isolated native fixture
and product attach tests with admitted Windows producers for those gates.
