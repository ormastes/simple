# Compiler and Language Feature Group

Base knowledge for syntax, semantic analysis, lowering, code generation,
bootstrap, diagnostics, native build, linking, and cache identity features.
Always combine this group with every selected compiler layer base.

## Literals (decision 2026-11-03, ADR-005)

- Single quotes mean ONLY `char`: one Unicode scalar (1-4 UTF-8 bytes) or one
  escape (`'\n'`, `'\''`, `'\u{1F600}'`). `'é'`, `'한'`, `'😀'` are chars;
  decomposed e + U+0301 or a ZWJ emoji is several scalars and is text.
- Text forms: `"..."` interpolates `{expr}`; `r"..."` / `r"""..."""` raw;
  `"""..."""` multi-line with literal braces. Never write new multi-scalar
  `'...'` raw strings (guard `scripts/check/check-no-single-quoted-raw-string.shs`).
- `s[i]` indexes by code point, `.len()` counts code points (staged),
  `.byte_len()` / `byte_at` are byte-level. A `char` is not a condition
  (`if c:` is a type error; write `c != '\0'`).
- The lexer switch lands only after the stage3 self-build passes; staged
  warnings become errors once Windows, macOS and Linux all have a self-hosted
  binary. Bug row: `char_literal_lexer_switch_staged_2026-11-03`.
