# Char Index Policy (ADR-005)

> `s[i]` yields a `char` code point; interpreter and JIT agree, including out of range.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Requirement | ADR-005 `doc/04_architecture/adr/ADR-005-text-index-yields-char.md` |
| Source | `test/03_system/language/policy/char_index_spec.spl`, `char_index_in_dev_spec.spl` |
| Generator | hand-written (spipe-docgen not run) |

## Scenarios

| # | Scenario | Status |
|---|----------|--------|
| 1 | Index ASCII by code point | passing |
| 2 | Index 2-byte char as one element | passing |
| 3 | Index 3-byte char as one element | passing |
| 4 | Index 4-byte char as one element | passing |
| 5 | Negative indices count from the end in code points | passing |
| 6 | `s[i] as i64` is the code point | passing |
| 7 | `s[i].to_text()` is 1-character text | passing |
| 8 | `chars()` yields one element per code point | passing |
| 9 | `char_count()` counts code points | passing |
| 10 | `byte_at()` reads UTF-8 bytes | passing |
| 11 | `char_code_at()` reads the code point | passing |
| 12 | `len()` counts bytes today (switch held) | passing |
| 13 | Interpreter and JIT give identical indexing output | passing |
| 14 | Out-of-range index is "index out of bounds" on the interpreter | passing |
| 21 | Out-of-range index is "index out of bounds" on the JIT (today: empty text, lanes diverge) | in-development |
| 15 | `to_digit()` returns Some/None | in-development |
| 16 | `to_digit()` None for non-digit | in-development |
| 17 | `char.from_code(n)` round-trips `ord()` on both lanes | in-development |
| 18 | `byte_len()` counts UTF-8 bytes | in-development |
| 19 | `len()` counts code points | in-development |
| 20 | `char == text` is a compile error | in-development |
