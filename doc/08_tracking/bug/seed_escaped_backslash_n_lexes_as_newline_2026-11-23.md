# Seed lexes `"\\n"` / `"\\t"` as a control character — 2026-11-23

Status: verification-pending (no seed code change; workaround removed).
Owner: Rust seed string-literal unescape (src/compiler_rust, lexer/parser).

## Re-investigation 2026-11-24 (lane se1): does not reproduce

Same deployed seed (`C:/dev/simple/bin/simple.exe`, 42497024 bytes, 2026-11-19
19:22). Source bytes checked with `od -c` (`" \ \ n "`):

| literal (real source bytes) | `.len()` |
|---|---|
| `"\\n"` | 2 |
| `"a\\nb"` | 4 |
| `"\\t"` | 2 |
| `"\\\\"` | 2 |
| `["a", "\\n"][1]` | 2 |

All correct. `process_escape` (parser/src/lexer/escapes.rs) consumes `\\` once.

The original table is reproduced exactly by feeding *single* backslashes
(`"\n"`=1, `"a\nb"`=3, `"\t"`=1, `"\N"`=2, `r"\n"`=2). So the original
measurement ran on source whose `\\` had been collapsed to `\` before it
reached the seed: a shell `printf`/tool-transport artifact, not the lexer. In
this session a heredoc written through the agent shell tool collapsed `\\n` to
`\n` the same way, while a file written directly kept the bytes.

`hir_codec_char_spec.spl` passes 5/5 on the deployed seed with the plain
`"\\n"` literal restored. Triple-quoted `"""\\n"""` stays 3 chars because
triple-quoted strings are raw by design (strings.rs `scan_triple_quoted_string`).

## Regression pins
- Rust: `parser/src/lexer_tests_literals.rs`
  `test_escaped_backslash_before_escape_letter_is_consumed_once`
- Spec: `test/01_unit/compiler/lexer/string_escaped_backslash_spec.spl` (5/5)

Lesson: write fixtures containing backslashes with a file-write tool, then check
bytes with `od -c` before filing a lexer bug.
