# String interpolation has no `{v:x}` hex format-spec

**Status:** documented limitation / feature request (not a defect in existing hex helpers)
**Found:** 2026-08-06, during aarch64 boot debugging (logs like `"0x{offset}"` print the
value in decimal, which is misleading in hex-context logs).

## What exists today

`src/lib/common/format.spl` already provides working hex formatting helpers:
- `format_hex(n: i64) -> text` — lowercase hex, no `0x` prefix (`255 -> "ff"`)
- `format_hex_upper(n: i64) -> text` — uppercase hex (`255 -> "FF"`)

These work correctly, including inside string interpolation, e.g.:
`"0x{format_hex(offset)}"` -> `"0xff"`.

Coverage: `test/01_unit/lib/common/format_spec.spl` (`format_hex` / `format_hex_upper`
describe blocks), including the interpolation cases and documented negative-input
behavior (`format_hex(-5)` returns `""` — the loop guard is `while num > 0`, so
negative input never enters the loop; this is a documented limitation, not a
spec guarantee of two's-complement or signed-hex formatting).

## What's genuinely missing

There is no grammar-level format-spec syntax in string interpolation
(`"{v:x}"`, `"{v:X}"`, `"{v:08x}"`, etc.) — confirmed by grepping
`src/app/desugar` for interpolation lowering: no `:x}`/format-spec handling
exists anywhere in the interpolation desugar path.

## Recommendation

Do not silently normalize the cosmetic decimal-in-log confusion by inventing
new grammar. The idiomatic fix already available today is
`"0x{format_hex(v)}"` instead of `"0x{v}"`. If `{v:x}` format-spec syntax is
wanted as a language feature, it should be scoped as a proper grammar change
(parser + lexer + desugar) and tracked separately — this doc records that gap
so it isn't rediscovered as a "hex formatting is broken" bug report again.
