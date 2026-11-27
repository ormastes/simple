# `core_reference_tokens_v1` byte_start/byte_end were codepoint offsets on non-ASCII sources

- **Date:** 2026-11-12
- **Status:** fixed — verification-pending (landed from lane diag-P1, `work/diag-p1-contract`)
- **Severity:** HIGH for diagnostics on any non-ASCII source — every LSP range after
  the first multi-byte character is shifted left, so CMM/Markdown/Simple diagnostics
  built on the shared parser-infra facade would point at the wrong columns.

## Symptom

`core_reference_tokens_v1("x = 1\ny = \"😀\" + zed\n", 100)` reported the `zed`
token at `byte_start=16..19`; the real byte span is `19..22`. Fed to
`std.common.diagnostics.source_position.span_to_range` (which is byte-correct),
the UTF-16 range came out as character 8 instead of 11.

## Root cause

`src/compiler/10.frontend/core/lexer_struct.spl` built its codepoint->byte
`offsets` table with `character.len()` and checked the total against
`source.len()`. On the seed `text.len()` counts code points, so the "byte"
table was a codepoint table (self-consistent, hence the invariant never fired).
`test/01_unit/compiler/frontend/lexer_reference_tokens_v1_spec.spl` codified the
same mistake (`ch.len()` and `source[byte_start:byte_end]` with a codepoint slice).
`src/compiler/20.hir/hir_reference_snapshot_v1.spl` bounded `byte_end` by
`source.len()` too, which would have rejected correct byte spans.

## Fix

- `lexer_struct.spl`: `character.byte_len()` / `source.byte_len()`; spelling is
  sliced by codepoint indices (`source[start:end]`), byte span from `offsets[]`.
- `hir_reference_snapshot_v1.spl`: bound by `source.byte_len()`.
- Spec repaired to byte offsets; new repro + prevention coverage in
  `test/01_unit/compiler/frontend/parser_infra_facade_v1_spec.spl` (Hangul literal
  byte span 18..26; emoji line projected to UTF-16 character 11..14).

## Prevention

Use `byte_len()` whenever a value is called a byte offset. `text.len()` semantics
differ by engine (see `entry_import_scanner_loses_imports_after_multibyte_utf8_2026-11-11.md`).
