# str_to_lower / str_to_upper crash on multibyte UTF-8 input

**Date:** 2026-08-18
**Found during:** C-MIG-0026 evidence-package work (differential test of
`std.common.string_core.str_to_lower` against the C oracle
`rt_text_to_lower_ascii`).
**Status:** RESOLVED (str_to_lower, str_to_upper, str_trim_left, str_trim_right,
str_replace_all, str_reverse) — see "Fix applied" and "Defect-class audit"
below. `str_split`'s empty-separator branch shares the crash SHAPE but not a
safe one-liner fix and is left OPEN as a remaining instance.
**Status:** OPEN

## Symptom

`str_to_lower` / `str_to_upper` (`src/lib/common/string_core.spl:312-338`)
crash with `semantic: string index out of bounds` whenever the input contains
any codepoint above ASCII (2/3/4-byte UTF-8), instead of passing those bytes
through unchanged the way the C oracle `rt_text_to_lower_ascii` /
`rt_text_to_upper_ascii` (`src/runtime/runtime_simd_case.c`,
`interpreter_extern/simd.rs:2108-2128`) does.

Repro:
```
use std.common.string_core.{str_to_lower}
val s = "CAF\u{e9}"
print("len={s.len()}")     # -> 5 (BYTE length: "CAF" + 2-byte é)
print(str_to_lower(s))     # -> semantic: string index out of bounds:
                            #    index is 4 but length is 4 (preview="CAFé")
```

## Root cause

`str_to_lower`/`str_to_upper` loop `while i < slen: val ch = s[i]`, where
`slen = s.len()`. `text.len()` returns the **byte** length (5 for `"CAF\u{e9}"`),
but single-bracket indexing `s[i]` (as opposed to range-slicing `s[a:b]`,
used elsewhere in this same file) is **codepoint**-indexed (4 codepoints for
the same string). The loop therefore walks past the last valid codepoint
index and the interpreter's bounds check fires.

Every other search/slice helper in `string_core.spl` (`str_ends_with`,
`str_starts_with`, `str_index_of`, `str_last_index_of`, `str_slice`, ...)
uses **range** slicing (`s[a:b]`), which turns out to be internally
consistent with `.len()` (both byte-based) — confirmed by direct test: a
`str_last_index_of` / `rt_string_rfind` differential over a multibyte-suffix
subject succeeds without error. Only the single-index form used by
`str_to_lower`/`str_to_upper` has this length/indexing-basis mismatch.

## Impact

Any pure-Simple caller of `str_to_lower`/`str_to_upper` with non-ASCII input
crashes instead of behaving like the C `_ascii` oracle it was written to
mirror. This blocked the natural C-MIG-0026 pairing
(`str_to_lower` vs `rt_text_to_lower_ascii`) — that migration target was
rejected in favor of `str_last_index_of` vs `rt_string_rfind` (unaffected
because it uses range slicing) to keep the evidence package itself honest and
green. See `test/01_unit/lib/common/string_core_to_lower_ascii_crosslang_spec.spl`
git history / commit message for the pairing that was tried first and hit
this crash on its multibyte KAT.

## Fix applied (2026-08-18)

Applied option (a): rewrote the single-bracket byte-position access `s[i]` /
`s[k]` as the byte-range slice `s[i:i+1]`, which is basis-consistent with
`.len()` (both byte-based) — matching every sibling function in the file that
already uses range slicing. ASCII case-mapping semantics are unchanged: only
`A-Z`/`a-z` still shift by 32; every other byte/codepoint passes through via
straight re-concatenation (`result.join("")`), which reconstructs the
original bytes exactly regardless of whether an intermediate 1-byte fragment
is itself a valid standalone UTF-8 sequence.

Fixed in `src/lib/common/string_core.spl`:
- `str_to_lower` (line ~317)
- `str_to_upper` (line ~331)
- `str_trim_left` (line ~116, via `is_whitespace_char(s[i:i+1])`)
- `str_trim_right` (line ~123, same)
- `str_replace_all` (line ~158, single-byte fallback branch)
- `str_reverse` (line ~351)

## Defect-class audit — other `s[i]`-vs-byte-`.len()` call sites in this file

Grepped `string_core.spl` for every `while i < s.len()` / `while i >= 0` loop
paired with single-bracket `s[i]` (as opposed to range-slice `s[a:b]`).
Found 7 sites total, all in the same file:

| function | line | fixed? | notes |
|---|---|---|---|
| `str_to_lower` | ~317 | yes | subject of this bug |
| `str_to_upper` | ~331 | yes | subject of this bug |
| `str_trim_left` | ~116 | yes | `is_whitespace_char(s[i:i+1])`; only string-equality-compares each byte, so per-byte walking is semantically safe |
| `str_trim_right` | ~123 | yes | same reasoning, reverse direction |
| `str_replace_all` | ~158 | yes | non-match fallback byte; re-concatenated byte-for-byte |
| `str_reverse` | ~351 | yes | fixed the CRASH; byte-level reversal of a multibyte codepoint's bytes was **already** a pre-existing semantic limitation of this byte-oriented helper (reversing "café" byte-wise does not yield a readable reversed string) — this fix does not introduce that, it only stops the crash. Verified: `str_reverse(str_reverse(x)) == x` byte-for-byte (reversal is its own inverse), and a single reversal no longer crashes and preserves byte length. |
| `str_split` (empty-separator branch, `result.push(s[k])`) | ~176 | **NO — left OPEN** | Unlike the others, this branch's *contract* is to split into per-**character** elements, not per-byte. A byte-range `s[k:k+1]` one-liner would stop the crash but silently change the returned array (a 2-byte codepoint becomes 2 separate invalid-partial-byte elements instead of 1 character element) — a data-contract change, not merely a crash fix. Needs real UTF-8 lead-byte-width detection (decode how many bytes the codepoint at position `k` occupies, slice that width) rather than this one-liner. Filed as a remaining instance of this defect class; not fixed in this pass. |

## Reproduce spec

`test/01_unit/lib/common/string_core_case_utf8_spec.spl` — pure-Simple only.
No C-oracle differential pairing exists here: `str_case_crosslang_spec.spl`
does not exist in this tree (checked), and the C-MIG-0026-era finding in this
doc (`str_to_lower` vs `rt_text_to_lower_ascii` was rejected as a pairing
target because it hit exactly this crash) means the honest scope for this
regression spec is pure-Simple contract verification, not a cross-language
oracle comparison.

Pre-fix crash (captured verbatim via `git stash` to the pre-fix tree, then
`bin/simple run` on a two-line repro using `str_to_lower("CAF\u{e9}")`):
```
[INFO] JIT compilation failed, falling back to interpreter: semantic: string index out of bounds: index is 4 but length is 4 (preview="CAFé")
error: semantic: string index out of bounds: index is 4 but length is 4 (preview="CAFé")
```

Post-fix: `bin/simple test test/01_unit/lib/common/string_core_case_utf8_spec.spl`
```
Results: 12 total, 12 passed, 0 failed
```

Existing `string_core` specs re-verified green post-fix (sequential runs):
`string_core_spec.spl` (2/2), `string_core_ops_spec.spl` (205/205),
`string_core_advanced_coverage_spec.spl` (153/153),
`string_core_basic_coverage_spec.spl` (266/266),
`string_core_exhaustive_spec.spl` (106/106),
`string_core_char_access_spec.spl` (2/2), `string_core_charcode_spec.spl`
(112/112), `string_core_ends_with_crosslang_spec.spl` (6/6),
`string_core_rfind_crosslang_spec.spl` (5/5),
`string_core_char_from_code_crosslang_spec.spl` (6/6) — all `0 failed`.
## Fix sketch (not applied here — out of scope for a C-MIG evidence task)

Applied option (a): rewrote the single-bracket byte-position access `s[i]` /
`s[k]` as the byte-range slice `s[i:i+1]`, which is basis-consistent with
`.len()` (both byte-based) — matching every sibling function in the file that
already uses range slicing. ASCII case-mapping semantics are unchanged: only
`A-Z`/`a-z` still shift by 32; every other byte/codepoint passes through via
straight re-concatenation (`result.join("")`), which reconstructs the
original bytes exactly regardless of whether an intermediate 1-byte fragment
is itself a valid standalone UTF-8 sequence.

Fixed in `src/lib/common/string_core.spl`:
- `str_to_lower` (line ~317)
- `str_to_upper` (line ~331)
- `str_trim_left` (line ~116, via `is_whitespace_char(s[i:i+1])`)
- `str_trim_right` (line ~123, same)
- `str_replace_all` (line ~158, single-byte fallback branch)
- `str_reverse` (line ~351)

## Defect-class audit — other `s[i]`-vs-byte-`.len()` call sites in this file

Grepped `string_core.spl` for every `while i < s.len()` / `while i >= 0` loop
paired with single-bracket `s[i]` (as opposed to range-slice `s[a:b]`).
Found 7 sites total, all in the same file:

| function | line | fixed? | notes |
|---|---|---|---|
| `str_to_lower` | ~317 | yes | subject of this bug |
| `str_to_upper` | ~331 | yes | subject of this bug |
| `str_trim_left` | ~116 | yes | `is_whitespace_char(s[i:i+1])`; only string-equality-compares each byte, so per-byte walking is semantically safe |
| `str_trim_right` | ~123 | yes | same reasoning, reverse direction |
| `str_replace_all` | ~158 | yes | non-match fallback byte; re-concatenated byte-for-byte |
| `str_reverse` | ~351 | yes | fixed the CRASH; byte-level reversal of a multibyte codepoint's bytes was **already** a pre-existing semantic limitation of this byte-oriented helper (reversing "café" byte-wise does not yield a readable reversed string) — this fix does not introduce that, it only stops the crash. Verified: `str_reverse(str_reverse(x)) == x` byte-for-byte (reversal is its own inverse), and a single reversal no longer crashes and preserves byte length. |
| `str_split` (empty-separator branch, `result.push(s[k])`) | ~176 | **NO — left OPEN** | Unlike the others, this branch's *contract* is to split into per-**character** elements, not per-byte. A byte-range `s[k:k+1]` one-liner would stop the crash but silently change the returned array (a 2-byte codepoint becomes 2 separate invalid-partial-byte elements instead of 1 character element) — a data-contract change, not merely a crash fix. Needs real UTF-8 lead-byte-width detection (decode how many bytes the codepoint at position `k` occupies, slice that width) rather than this one-liner. Filed as a remaining instance of this defect class; not fixed in this pass. |

## Reproduce spec

`test/01_unit/lib/common/string_core_case_utf8_spec.spl` — pure-Simple only.
No C-oracle differential pairing exists here: `str_case_crosslang_spec.spl`
does not exist in this tree (checked), and the C-MIG-0026-era finding in this
doc (`str_to_lower` vs `rt_text_to_lower_ascii` was rejected as a pairing
target because it hit exactly this crash) means the honest scope for this
regression spec is pure-Simple contract verification, not a cross-language
oracle comparison.

Pre-fix crash (captured verbatim via `git stash` to the pre-fix tree, then
`bin/simple run` on a two-line repro using `str_to_lower("CAF\u{e9}")`):
```
[INFO] JIT compilation failed, falling back to interpreter: semantic: string index out of bounds: index is 4 but length is 4 (preview="CAFé")
error: semantic: string index out of bounds: index is 4 but length is 4 (preview="CAFé")
```

Post-fix: `bin/simple test test/01_unit/lib/common/string_core_case_utf8_spec.spl`
```
Results: 12 total, 12 passed, 0 failed
```

Existing `string_core` specs re-verified green post-fix (sequential runs):
`string_core_spec.spl` (2/2), `string_core_ops_spec.spl` (205/205),
`string_core_advanced_coverage_spec.spl` (153/153),
`string_core_basic_coverage_spec.spl` (266/266),
`string_core_exhaustive_spec.spl` (106/106),
`string_core_char_access_spec.spl` (2/2), `string_core_charcode_spec.spl`
(112/112), `string_core_ends_with_crosslang_spec.spl` (6/6),
`string_core_rfind_crosslang_spec.spl` (5/5),
`string_core_char_from_code_crosslang_spec.spl` (6/6) — all `0 failed`.
