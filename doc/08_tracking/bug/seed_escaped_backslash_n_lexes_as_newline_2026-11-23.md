# Seed lexes `"\\n"` / `"\\t"` as a control character — 2026-11-23

Status: open; workaround tagged in test/01_unit/compiler/hir/hir_codec_char_spec.spl.
Owner: Rust seed string-literal unescape (src/compiler_rust, lexer/parser).

Measured on the deployed Windows seed `bin/simple.exe` (2026-11-19 build), in a
spec run through the interpreter:

| literal | bytes produced | expected |
|---|---|---|
| `"\\n"` | `[10]` | `[92, 110]` |
| `"a\\nb"` | `[97, 10, 98]` | `[97, 92, 110, 98]` |
| `"\\t"` | `[9]` | `[92, 116]` |
| `"\\N"` | `[92, 78]` | `[92, 78]` (correct) |
| `r"\n"` | `[92, 110]` | `[92, 110]` (correct) |

So an escaped backslash followed by a known escape letter gets unescaped a second
time, the same class as gdb_mi_literal_backslash_escape_2026-11-07.md. Effect:
`hir_codec_char_spec` built the wire `"4\n" + "\\n" + "\n"` as
`4\n\n\n`, the codec read an empty char line and correctly rejected it with
`invalid_char_scalar`. The codec was not at fault.

Workaround: the spec writes the escaped-newline payload as `r"\n"`.
Fix: consume each escape once in the seed literal unescape; then drop the
workaround tag and restore the plain `"\\n"` literal.
