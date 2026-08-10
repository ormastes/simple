# `char_from_code(0)` returns a NUL byte, spec expects empty text

- **ID:** char_from_code_zero_returns_nul_not_empty_2026-08-10
- **Status:** RED (1 of 205 in both trees)
- **Binary:** `src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime 2026-08-09 23:10)

## Verdict after `8e119d13780`

```
SPEC FILE VERDICT: test/01_unit/lib/common/string_core_ops_spec.spl declared>=205 executed=205 passed=204 failed=1 dropped=0
SPEC FILE VERDICT: test/unit/lib/common/string_core_ops_spec.spl      declared>=205 executed=205 passed=204 failed=1 dropped=0
```

Before the fix this file was `executed=205 passed=180 failed=25`. The 24
search-primitive failures (`str_index_of` / `str_last_index_of` returning -1
unconditionally, `str_ends_with` returning 0) are gone. One failure remains,
and it is a different, pre-existing defect.

## The remaining failure

`test/01_unit/lib/common/string_core_ops_spec.spl:713` (and the `test/unit`
twin):

```
it "returns empty for unknown code":
    expect(char_from_code(0)).to_equal("")
```

reports `expected   to equal ` — both sides *print* as empty, which is why the
message looks vacuous. They are not equal: the actual value is a one-byte
string containing U+0000.

`src/lib/common/string_core.spl:204` `char_from_code_inline`:

- code 0 is not one of the 9/10/11/12/13 specials,
- not in the 32..126 ASCII table,
- and the reject test at line 224 is
  `code < 0 or code > 0x10FFFF or (code >= 0xD800 and code <= 0xDFFF)` — U+0000
  passes all three, so it falls through to the UTF-8 encoder and returns
  `"\u0000"`.

## Conflict to resolve (do not paper over)

The spec asserts code 0 is "unknown" and yields empty text. The implementation
comment says only *invalid* codepoints return empty, and U+0000 is a valid
codepoint. Both are internally consistent; they disagree with each other.

Options, in preference order:

1. Treat U+0000 as non-representable in `text` and return `""` — matches the
   spec and avoids embedding NUL bytes in text values (a real hazard for the
   C-string paths in `src/runtime/`). Requires adding `code == 0` to the reject
   condition at `string_core.spl:224`.
2. Keep encoding U+0000 and rewrite the spec expectation to
   `expect(char_from_code(0).len()).to_equal(1)` — but that changes an
   assertion to match the implementation, which is exactly what
   `.claude/rules/testing.md` forbids without a deliberate ruling.

Left RED pending that ruling. The matcher message is also unhelpful here: it
renders a NUL byte as nothing, so the failure reads as `expected   to equal `.
Worth a separate matcher-rendering improvement (escape non-printables in
`to_equal` failure output).
