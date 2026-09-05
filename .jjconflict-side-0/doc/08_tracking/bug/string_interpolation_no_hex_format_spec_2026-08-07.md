# String interpolation has no `{v:x}` hex format-spec

**Status:** confirmed-as-designed (no format-spec grammar) — BUT the recommended
workaround was itself broken for addresses, and that half is now FIXED
(2026-08-09). See "2026-08-09 re-verification" at the bottom.
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

## 2026-08-09 re-verification — the premise is confirmed, the workaround was not

Re-opened as "`"0x{address}"` prints DECIMAL, not hex". Two separate questions;
they resolve in opposite directions.

### 1. "Interpolation should format hex" — FALSE PREMISE, confirmed

No format-spec syntax exists anywhere in the grammar or the interpolation
desugar path. A grep for `format_spec` / `FormatSpec` / `:x}` / `:08x` across
`src/compiler/**` and `src/app/desugar/**` returns **zero** Simple-grammar hits
— the only matches are Rust `format!("{{:x}}")` *string templates* inside
`src/compiler/90.tools/sffi_gen/specs/crypto_mod.spl`, i.e. text the SFFI
generator emits into generated Rust, not Simple syntax.

So `"0x{v}"` is exactly what it looks like: the two literal characters `0x`
followed by `v` rendered with the default (decimal) conversion. It never
promised hex, and nothing is miscompiling. Measured: `"0x{255}"` -> `0x255`
on both `SIMPLE_EXECUTION_MODE=interpreter` and `=jit` via
`bin/simple run` (the Rust **seed**). Correct spelling remains
`"0x{format_hex(v)}"` -> `0xff`.

### 2. The recommended workaround silently printed NOTHING for real addresses

This is the part that was actually broken, and it is the same invisible-failure
class the original report was reaching for. `format_hex`'s loop guard was
`while num > 0`, so **every negative input returned `""`** — and any address at
or above `0x8000000000000000` *is* a negative `i64`. The advice "use
`0x{format_hex(addr)}`" therefore turned a misleading-but-present decimal into
a blank:

```
format_hex(-1)  -> ""      (want ffffffffffffffff)
format_hex(-5)  -> ""      (want fffffffffffffffb)
```

`format_hex_upper` had the identical guard and the identical hole. There are
**228** `"0x{...}"` interpolation sites in `src/**` (pointer/breakpoint/PC/
sentinel diagnostics in `debug/remote`, `replay/process`, the Mach-O/PE
inspectors, the loader's `object_mapper`), so this was the on-ramp for every
one of them.

**Fixed** in `src/lib/common/format.spl`: `format_hex` / `format_hex_upper` now
share a `format_hex_digits` helper that formats negative values as their
two's-complement 64-bit form via masked shifts (`(n >> shift) & 15`), instead
of falling out of a `> 0` guard as empty text. Positive and zero paths are
byte-identical to before.

Verified on **both** engines through `bin/simple run` (Rust seed):
`-1 -> ffffffffffffffff`, `-5 -> fffffffffffffffb`,
`-9223372036854775808 -> 8000000000000000`, `255 -> ff`, `0 -> 0`,
`format_hex_upper(-1) -> FFFFFFFFFFFFFFFF`.

Spec: `test/01_unit/lib/common/format_spec.spl` — **25 examples, 0 failures**.
The pre-existing example that *asserted* the empty-string behaviour as a
"documented limitation" was replaced, since it pinned the defect in place.

Sabotage-tested (compilable change, real verdict): changing the new loop guard
to `while i < 0` — which restores the old empty-string result without breaking
compilation — turns exactly the 4 new assertions red
(`expected  to equal fffffffffffffffb`, `... ffffffffffffffff`,
`... 8000000000000000`, `... FFFFFFFFFFFFFFFF`), `25 examples, 4 failures`,
rc=1. Guard restored afterwards; spec green again.

### Not done, deliberately

The 228 `"0x{v}"` call sites are **not** mechanically rewritten to
`"0x{format_hex(v)}"` here. Now that `format_hex` handles the full `i64` range
that rewrite is finally *safe*, but it is a 228-site bulk edit across unrelated
subsystems and belongs in its own reviewed lane rather than riding along with
the library fix.
