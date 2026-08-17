# Bracket-slice byte-index survey — fix pass 1 (2026-07-29)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Follow-up to `doc/08_tracking/bug/bracket_slice_byte_index_survey_2026-07-29.md`.
Fixes the 4 files that survey flagged as "missed-HIGH" (matched the HIGH-risk
domain but the keyword classifier didn't catch them):
`src/lib/common/js/builtins/string.spl`, `.../number.spl`,
`src/lib/nogc_sync_mut/glob.spl` (+ its byte-identical mirror
`src/lib/nogc_async_mut/glob.spl`), `src/app/doc_coverage/scanner/comment_extractor.spl`.

Per-file: PROVED vs INFERRED, fix or "no bug found" verdict, multi-byte
evidence.

## 1. `src/lib/common/js/builtins/string.spl` — FIXED (2 real bugs)

**Bugs found (PROVED, direct code reading):**
- `string_charAt(s, index)`/`string_charCodeAt` treated `index` as a BYTE
  offset (`s[index:index+1]`) while their name and every caller-facing
  contract implies JS character-index semantics. For any character after a
  multi-byte one, this read a stray UTF-8 continuation byte instead of the
  requested character. `string_charCodeAt` additionally called
  `ch.byte_at(0)` to get "the codepoint value" — **`.byte_at()` does not
  exist as a text method on this seed** (`semantic: method 'byte_at' not
  found on type 'str'` — confirmed by direct compile error, not
  inference); this function could not have run successfully for ANY input,
  confirming it was fully dead code, not just multi-byte-unsound.
- `string_split(s, "")` pushed one BYTE per array element
  (`chars.push(s[i:i+1])`, `i += 1` always) instead of one character —
  shredded every multi-byte character into multiple invalid single-byte
  fragments.

**Fix:** walk `text_codepoints(s)` (already byte-consistent stdlib
function) and sum `utf8_codepoint_byte_len(cp)` to find each character's
real byte range, then do one plain byte-indexed bracket-slice. Never calls
`char_at` (character-indexed — the exact mismatch class this survey
hunts) and, after a diagnosed false start, never routes a byte-range
through a tuple-returning helper (see "aggregate-return landmine" below) —
every intermediate value is a scalar local, one call deep.

**Confirmed dead-code / zero regression risk:** `grep`'d the whole repo —
`string_charAt`/`string_charCodeAt` have zero callers anywhere outside this
file (module `std.js.builtins.string` is imported by `js/mod.spl`, but only
for other symbols; `string_charAt` itself is never referenced). Changing
their semantics cannot regress any existing caller.

**Multi-byte evidence (PROVED via direct interpreter execution — see
"harness caveat" below for why not via the sspec run):**
```
s = "日本語": charAt(0)="日" charAt(1)="本" charAt(2)="語"
s = "a—b":   charAt(1)="—"  charCodeAt(1)=8212 (U+2014 EM DASH)
s = "café":  charAt(3)="é"  charCodeAt(3)=233 (U+00E9)
split("日本語","") -> ["日","本","語"] (3 elements, not 9 bytes)
```
Spec: `test/01_unit/lib/common/js/builtins/string_multibyte_spec.spl` (7
cases: café charAt, café charCodeAt, CJK charAt, em-dash charAt/charCodeAt,
café split, CJK split, pure-ASCII regression guard).

## 2. `src/lib/common/js/builtins/number.spl` — NO BUG FOUND

Read the full file (`number_parseInt`, `number_parseFloat`, and all
`toFixed`/`toPrecision`/`toExponential`/`toString` formatters). Every
bracket-slice site walks `i` one byte at a time only while scanning for
ASCII digit/sign/decimal-point bytes, and the scan **stops the instant it
sees any non-digit byte** (`if digit < 0: break`). A UTF-8 continuation or
lead byte (>= 0x80) can never equal an ASCII digit byte (0x30-0x39), so the
scan correctly terminates at the right position regardless of what
multi-byte content follows a numeric prefix — same "detects an ASCII
delimiter, safe" pattern the original survey confirmed for `json.spl`. No
`char_at` usage anywhere in the file. **No code change made.**

## 3. `src/lib/nogc_sync_mut/glob.spl` + `src/lib/nogc_async_mut/glob.spl` — FIXED (2 real bugs, 1 perf-only cleanup)

Byte-identical mirrors; same fix applied to both, re-diffed identical after.

**Bugs found (PROVED, direct code reading + concrete counterexample):**
- `?` wildcard advanced the path cursor `si` by exactly 1 byte
  (`_glob_at(si: si + 1, ...)`) regardless of the character at that
  position. For a multi-byte character this left `si` on a continuation
  byte, which can never equal the next (ASCII) pattern byte, so `?` could
  never match a real single multi-byte character. Counterexample:
  `glob_match("abéd", "ab?d")` — should be `true` (`?` = "é"), old code
  returns `false`.
- Negated character class `[!...]` (e.g. `[!/]`, "anything but a path
  separator") correctly decided a multi-byte character satisfies "not in
  this class", but only ever consumed 1 byte of it (`s[si:si+1]` /
  `si + 1`), leaving a stray continuation byte that corrupts every
  subsequent match step for that path.

**Perf-only cleanup, not a bug fix (documented as such, not overclaimed):**
`*` backtracking tried every byte position including mid-character splits.
Proved by exhaustion (continuation bytes 0x80-0xBF can never equal an
ASCII pattern byte or a valid UTF-8 lead byte 0xC2+, so a split-position
attempt can never produce a different final answer, only wasted recursion)
that stepping by whole codepoints instead is behavior-identical, not a
defect fix.

**Landmine hit and fixed while implementing:** the first version of the
`?` fix called `_glob_codepoint_len_at(s, si)` inline as an argument
expression (`si: si + _glob_codepoint_len_at(s, si)`) — under direct
interpreter execution this silently returned the wrong `si` for 3-byte
codepoints while the identical logic extracted to a local `val step = ...`
first was correct. Filed as new evidence for the project's known
"aggregate/nested-call-across-boundary" landmine family
(`doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md`).
Fixed by extracting every helper-call result to a local before using it, in
both the `?` branch and the `*` loop's step increment.

**Multi-byte evidence (PROVED via direct interpreter execution):**
```
glob_match("café.txt", "caf?.txt")     -> true
glob_match("日report.txt", "?report.txt") -> true
glob_match("a—b", "a?b")               -> true
glob_match("café.txt", "caf??txt")     -> false (one '?' too many, correct reject)
```
Spec: `test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl` (9 cases:
`?` over café/CJK/em-dash, over-length reject, `*` regression, negated
class over multi-byte, positive-class reject, literal multi-byte match,
pure-ASCII regression guard).

## 4. `src/app/doc_coverage/scanner/comment_extractor.spl` — NO BUG FOUND in bracket-slice indexing; one adjacent, separately-tracked issue noted

All bracket-slice sites (`rest[0:content_len]`, `line[0:end_idx]`,
`line[hash_idx+1:]`, `trimmed[3:]`) are fed byte-consistent indices:
`content_len = rest.len() - 3` (byte length minus the 3-byte `"""`
marker), `end_idx`/`hash_idx` from `.index_of(...)`. No `char_at` usage. No
bracket-slice bug. **No code change made.**

**Adjacent finding, not fixed here (separately tracked, pre-existing):**
`count_char` (used to detect whether a `#` sits inside a string literal, by
counting `"` occurrences before it) uses `for c in s:` — the exact idiom
`doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`
documents as corrupted on this seed's shared for-loop/text infrastructure.
That doc's own status line says "SOURCE FIXED (2026-07-22), rebuilt
current-source execution pending" — i.e. this is a known, already-tracked,
T3-tier compiler defect with its own filed bug, not something to
speculatively patch here; flagging that `comment_extractor.spl` is a live
call site is the useful new information, not a fix.

## Harness caveat (read before re-running any of the specs above)

`bin/simple test <spec>` gave **wrong (red) results** for both new specs
above, while the identical fixed source, run directly
(`bin/simple <plain-script>.spl` wrapping the same calls in `fn main()`),
gave **correct (green) results** for every case, verified 2x per file.
Root-caused to a genuine `bin/simple test`-vs-direct-execution divergence,
unrelated to these fixes — see
`doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md` for
the full repro and evidence. Do not read a red `bin/simple test` run of
these two specs as the fixes being wrong; re-verify via direct execution
per that doc until the harness bug is fixed.

## Landing

This doc + `test_harness_execution_divergence_2026-07-29.md` +
`string.spl` + `glob.spl` (both copies) +
`string_multibyte_spec.spl` + `glob_multibyte_spec.spl`. `number.spl` and
`comment_extractor.spl` unchanged (no bug found). No gate/budget files
touched.
