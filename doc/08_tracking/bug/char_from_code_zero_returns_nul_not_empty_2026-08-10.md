# `char_from_code(0)` returns a NUL byte, spec expected empty text

- **ID:** char_from_code_zero_returns_nul_not_empty_2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  was right. Assertion corrected in all four spec copies; implementation
  unchanged except for a comment recording the ruling.
- **Binary:** `src/compiler_rust/target/bootstrap/simple`, 33,759,648 bytes,
  mtime 2026-08-10 03:47 (shared seed).

## Original symptom

`test/{01_unit,unit}/lib/common/string_core_ops_spec.spl:713` asserted

```
it "returns empty for unknown code":
    expect(char_from_code(0)).to_equal("")
```

and failed, leaving `executed=205 passed=204 failed=1` in both trees (down from
25 failures before `8e119d13780`). The same assertion also existed at
`string_core_advanced_coverage_spec.spl:224` in both trees.

`src/lib/common/string_core.spl` `char_from_code_inline`: code 0 is not one of
the 9/10/11/12/13 specials, not in the 32..126 ASCII table, and the reject test
`code < 0 or code > 0x10FFFF or (code >= 0xD800 and code <= 0xDFFF)` does not
cover it — so it falls through to the UTF-8 encoder and returns a one-byte
U+0000.

## Diagnostic trap (worth knowing generally)

The failure renders as

```
expected   to equal
```

— an **invisible diff**. The matcher prints a NUL byte as nothing, so both
sides appear empty and the message reads as vacuous. Anyone triaging by
eyeballing the matcher output would conclude the two values are identical. The
only way to see the difference is to compare `.len()`. Any matcher failure
whose rendered expected/actual are both blank should be re-checked with an
explicit length or byte-level probe before being believed.

## Ruling: U+0000 is a legitimate character — do NOT reject it

The bug doc originally listed "add `code == 0` to the reject condition" as the
preferred option. **That option is actively dangerous** and was rejected on
evidence.

### Evidence 1 — the only production callers require a real NUL

`/usr/bin/grep -rn 'char_from_code(0)' src/` finds exactly three non-test
callers, all in the bootstrap-critical lexer:

- `src/compiler/10.frontend/core/lexer.spl:331` (`lex_cur_text_set`)
- `src/compiler/10.frontend/core/lexer_struct.spl:426` (`make_token`)
- `src/compiler/10.frontend/core/lexer_struct.spl:799` (triple-quote string)

All three use the identical shape:

```
val nul = char_from_code(0)
if tok_text.contains(nul):
    core_token_text_save("")
else:
    core_token_text_save(tok_text)
```

i.e. `char_from_code(0)` is used to construct a NUL **needle**, to detect token
text that contains an embedded NUL and blank it before it reaches `rt_env_set`
/ the C-string paths in `src/runtime/`. The guard exists precisely *because*
NUL is representable in `text` and must be kept out of C-string boundaries.

### Evidence 2 — returning `""` would make the needle match everything

Measured probe, both engines, seed 33,759,648:

```
abc_contains_empty   = true
empty_contains_empty = true
```

`s.contains("")` is unconditionally `true`. So if `char_from_code(0)` returned
`""`, every one of those three `if ...contains(nul)` guards would take the
true branch for **every token**, and the lexer would save `""` as the text of
every token it ever produced — a silent, total corruption of the bootstrap
token-capture and `SIMPLE_BOOTSTRAP_LEX_CUR_TEXT` env-save paths. No spec
covers that path, so it would have landed green.

### Evidence 3 — Unicode

U+0000 is a valid Unicode scalar value. It is not a surrogate, it is not above
U+10FFFF, and it is not negative. It is exactly as encodable as U+0001. The
implementation's stated policy ("reject *invalid* codepoints") is coherent and
correctly excludes 0 from rejection. The spec's label "unknown code" was simply
a misclassification: 0 is C0 NUL, a known character.

### Conclusion

The implementation is correct. The spec asserted a behaviour that, if
implemented, would break the compiler's own lexer. Fixed the spec.

## Fix

Implementation (`src/lib/common/string_core.spl`): behaviour **unchanged**;
added a comment above the reject condition stating that U+0000 is deliberately
not rejected and naming the three lexer callers, so a future "tidy-up" does not
re-introduce the hazard.

Specs — all four copies, assertion replaced with a stronger one that pins both
halves of the contract:

- `test/01_unit/lib/common/string_core_ops_spec.spl`
- `test/unit/lib/common/string_core_ops_spec.spl`
- `test/01_unit/lib/common/string_core_advanced_coverage_spec.spl`
- `test/unit/lib/common/string_core_advanced_coverage_spec.spl`

```
it "encodes U+0000 as a one-byte NUL and rejects invalid codepoints":
    val nul = char_from_code(0)
    expect(nul.len()).to_equal(1)
    assert_false(nul == "")
    expect(char_from_code(-1)).to_equal("")
    expect(char_from_code(0x110000)).to_equal("")
    expect(char_from_code(0xD800)).to_equal("")
```

This is a net *increase* in coverage: the previous test asserted one wrong
thing; the replacement asserts the real NUL contract plus the three
invalid-codepoint classes (negative, above-range, surrogate) that were
previously untested. It is kept as a single `it` block so the declared example
count stays at 205.

## Both-engine verification

`char_from_code(0)` behaviour is identical under the interpreter and the
JIT (`SIMPLE_EXECUTION_MODE=interpreter` vs `=jit`, same seed):

```
withnul_len          = 3      # "a" + NUL + "b"  -> NUL is exactly 1 byte
withnul_contains_z   = true
empty_eq             = false  # char_from_code(0) != ""
```

No engine divergence on this primitive.
