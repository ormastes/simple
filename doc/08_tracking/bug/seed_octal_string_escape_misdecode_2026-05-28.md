# Bug: Seed compiler mis-decodes octal string escapes

- **ID:** seed_octal_string_escape_misdecode
- **Severity:** P2
- **Date:** 2026-05-28
- **Area:** compiler / lexer (string-literal escape decoding)
- **Status:** open

## Summary

Octal string escapes are decoded incorrectly. `"\033"` (octal ESC) is emitted as
the byte sequence `0x00 '3' '3'` instead of the single ESC byte `0x1b`. This
corrupts every ANSI escape sequence written with octal notation.

## Impact

Breaks terminal/TUI rendering wherever `\NNN` octal escapes are used. Observed
across ~8 library files (`cli/*`, `tui/style.spl`, `mcp_sdk`, `tui/terminal.spl`).
Found while bringing up the editor TUI — alt-screen and color sequences written
with `\033` produced garbage bytes.

## Reproduce

A literal `"\033[2J"` should lex to `ESC [ 2 J` (4 bytes) but produces
`0x00 '3' '3' '[' '2' 'J'`. The hex form `"\x1b[2J"` decodes correctly.

## Workaround (in tree)

Converting `\033` → `\x1b` works. 15 sites in
`src/lib/nogc_sync_mut/tui/terminal.spl` were converted; ~4 octal sites remain on
`main`, and other lib files still use `\033`.

## Proposed fix

Fix octal escape decoding in the string-literal lexer — pure-Simple lexer first
(self-hosted path), then the Rust seed lexer (native-build path). Add a lexer
unit test covering `\0`, `\033`, `\377` boundaries. Optionally revert the `\x1b`
workarounds to canonical forms afterward.

## Location

- `src/lib/nogc_sync_mut/tui/terminal.spl` (workaround + remaining sites)
- Lexer: pure-Simple lexer under `src/compiler/` + Rust seed lexer under
  `src/compiler_rust/`
