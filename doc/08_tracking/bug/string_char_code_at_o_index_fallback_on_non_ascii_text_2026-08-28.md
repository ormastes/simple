# `text.char_code_at(i)` is O(i) on any string containing a non-ASCII byte at or before `i`

**Status:** open, recorded during the 2026-08-28 loader profile (not fixed there: the
runtime is outside that lane's edit scope, and no loader hot loop currently trips it).

## Mechanism

`rt_string_char_code_at` (`src/runtime/runtime_native.c:2731`) answers in O(1) only
while the requested CHARACTER index lies inside the string's ASCII prefix
(`SIMD_CACHE_FLAG_IS_ASCII` cached flag, or `rt_str_first_non_ascii(data,len) > index`).
As soon as the first multi-byte codepoint sits at or before `index`, it falls back to
the original "walk UTF-8 from byte 0" decode loop, so `while i < s.len(): s.char_code_at(i)`
is O(n^2) again for that string -- the exact shape the 2026-07 fix in that function
was written to remove, now conditional on content.

## Exposure

- 4,620 `.spl` files under `src/compiler`, `src/app`, `src/lib` contain at least one
  non-ASCII byte (`grep -rlP '[^\x00-\x7F]'`), typically an em-dash or arrow in a
  comment near the top of the file; 245 of them are in `src/compiler/{00.common,10.frontend,80.driver}`.
- Any whole-content `char_code_at` scan over such a file pays the walk from byte 0 on
  every call after the first non-ASCII byte.
- `rt_string_byte_at` (same file, just below) IS O(1) and is the right primitive for
  byte-framed scans (NUL checks, ASCII delimiter scans). The loader profile switched
  `env_value_nul_free` (`src/compiler/10.frontend/core/lexer_struct.spl`) to it for
  that reason.

## Suggested fix (runtime owner)

Cache, per string, the (byte_index, char_index) pair of the last decode so a
monotonically increasing scan resumes from the previous position instead of byte 0
(strings are immutable, so the cache is sound), or expose a codepoint iterator.
Keep `rt_string_byte_at` as the documented O(1) byte primitive.

## Regression pin idea

A spec that times `char_code_at` over a 256 KB string whose first byte is `é`
against the same string prefixed with an ASCII byte; the ratio must stay bounded
(< 3x), not grow with length.
