# Bracket-slice byte-index survey — fix pass 2 (2026-07-29)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Batch 2, follow-up to `bracket_slice_fix_pass_1_2026-07-29.md` (`1bd388912f5`)
and the harness root-cause (`9186d5daa73`). Per the harness finding,
`bin/simple test` is NOT used as the gate here — every claim below is
proved via direct execution (`bin/simple probe.spl`), with a vacuity probe
(run the unfixed source against the same input) for each real bug, and an
A/B check under `SIMPLE_EXECUTION_MODE=interpret` for any fix with
recursion or multi-branch control flow that could risk the interpreter
engine bug from the harness-divergence doc.

## New bug class discovered this pass: single-index `text[i]` is CHARACTER-indexed

Distinct from the `char_at()` mismatch the survey already documented.
Directly probed:
```
val s = "café"
s[0] = "c"   s[1] = "a"   s[2] = "f"   s[3] = "é"   (whole 2-byte char, not a byte)
s.len() = 5 (bytes) -- but s[4] is out of range (only 4 CHARACTERS exist)
```
Plain single-index access `text[i]` (no colon — distinct from the
`text[i:j]` slice form the original survey grepped for) returns the
i-th **character**, not the i-th byte. Every file below that mixed
`raw[pos]` (character-indexed) with `raw[a:b]` (byte-indexed, using the
same `pos`) has exactly the survey's byte/char mismatch bug, just via a
syntax form the original grep pattern (`\[[a-z_0-9 +*-]+:[a-z_0-9 +*-]*\]`,
which requires a colon) didn't catch. Worth a follow-up grep sweep of the
remaining HIGH file list for `[a-z_]\[[a-z_]*\][^:]` (single-index, no
colon) specifically — this pass found it in 2 of ~9 files checked (a ~22%
hit rate on this narrow check), higher than expected.

## 1. `src/app/devhub/convert_storage.spl` — FIXED (crashing bug, 5 sites)

`storage_to_markdown`'s main loop, its `_find_char`/`_extract_tag_name`
helpers, and `_replace_pairs` (the bold/italic/code marker-pair matcher
used by `markdown_to_storage`, the reverse direction) all walked
Confluence storage XHTML / Markdown via single-index `storage[i]`, `s[i]`,
`trimmed[end]` while feeding the resulting positions into byte-indexed
slices (`storage[i+1:tag_end]`, `storage[i:macro_end]`, `s[i:i+mlen]`,
etc.) one function away. `_replace_pairs` was missed on the first read of
this file and only caught on a second pass — worth remembering when
auditing "just a few sites" files: re-grep after the first fix, don't
trust the first pass's site count as exhaustive.

**Concrete pre-fix failure (PROVED, not inferred — direct execution):**
```
storage_to_markdown("<p>café text</p><h1>Title</h1>")
-> error: semantic: string index out of bounds: index is 30 but length is 30
```
A hard crash, not silently-wrong output — the char-space cursor walked
past the byte-space string's actual length once "é" (1 character, 2
bytes) desynced the two.

**Fix:** every single-index read converted to a byte-indexed 1-byte slice
— `storage[i]`/`s[i]`/`trimmed[end]` → `storage[i:i+1]`/`s[i:i+1]`/
`trimmed[end:end+1]` — matching every other slice already in the same
functions, across all 5 sites (main loop, `_find_char`,
`_extract_tag_name`, `_replace_pairs`). Minimal-diff fix; the loops'
control flow (`i`/`end` stepping by 1) is otherwise unchanged, so this is
purely an accessor-syntax change, not a rewrite.

**Verified (PROVED, direct execution, before/after):**
```
BEFORE: storage_to_markdown("<p>café text</p><h1>Title</h1>")  -> crash
AFTER:  storage_to_markdown("<p>café text</p><h1>Title</h1>")  -> "café text\n\n# Title"
AFTER:  storage_to_markdown("<p>日本語</p><h2>見出し</h2>")     -> "日本語\n\n## 見出し"
AFTER:  storage_to_markdown("<p>a—b</p><strong>bold</strong>") -> "a—b\n\n**bold**"
AFTER:  storage_to_markdown("<em>café日本語—end</em><p>done</p>") -> "*café日本語—end*done"
AFTER:  storage_to_markdown(pure-ASCII input)                   -> unchanged vs. pre-fix
AFTER:  markdown_to_storage("Body **bold café** text")          -> "<p>Body <strong>bold café</strong> text</p>"
```
No recursion in this file (plain `while` loops only) — per the harness
divergence doc's scoping note, non-recursive shapes were confirmed safe
under the interpreter even in that investigation, so this fix's risk is
low; A/B'd anyway: **default engine and `SIMPLE_EXECUTION_MODE=interpret`
agree**, both correct.

Spec: `test/01_unit/app/devhub/convert_storage_multibyte_spec.spl` (6
cases). Not run through `bin/simple test` per the harness caveat — proved
via direct execution instead (see above).

## 2-4. `gdb_mi_parser.spl` (3 copies) — FIXED (same bug class, higher impact)

`src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser.spl` +
byte-identical mirror `src/lib/nogc_async_mut/...` + a third,
non-identical copy `src/app/debug/remote/protocol/gdb_mi_parser.spl`
(has extra `GdbBreakpoint` class content, but the same parser functions).
GDB Machine Interface protocol parser — carries arbitrary debuggee string
values (variable contents, paths), a HIGH-risk domain the survey named
directly.

**Same bug, more sites:** `find_char`/`find_closing_quote`/
`find_matching_brace`/`find_matching_bracket` (the file's own comment even
flags them as a deliberate `index_of` replacement — "BUG-RT-010: index_of()
returns Option, not i32. Use split() or find_char()" — replacing one bug
with another) all walked via single-index `raw[pos]`, plus two more
single-index reads at the call sites (`trimmed[0]`, `raw[pos]` for the
value-type dispatch, `inner[pos]` for tuple-list scanning). Every one of
these functions' return values gets fed straight into a byte-indexed
`raw[a:b]` slice by every caller (`parse_class_and_data`,
`parse_kv_pairs`, `parse_tuple_records`).

**Concrete pre-fix failure (PROVED — vacuity probe against the actual
pre-fix source, not a hypothetical):**
```
BEFORE parse_line('*stopped,reason="café-hit",value="42"')
  -> reason="café-hi" (truncated, missing trailing "t"), value KEY MISSING ENTIRELY
BEFORE parse_line('^done,name="日本語",id="7"')
  -> name="日" (truncated to 1 of 3 characters), id KEY MISSING ENTIRELY
BEFORE parse_line('*stopped,frame={func="a—b",line="5"}')
  -> frame={func="a—b",line="5  (truncated, missing closing "} )
BEFORE parse_line('^done,reason="exited",code="0"')  (pure ASCII)
  -> correct in both versions (regression guard)
```

**Fix:** every single-index text read converted to a byte-indexed 1-byte
slice (`raw[pos]` → `raw[pos:pos+1]`, etc.), applied identically to all 3
copies (sed-verified zero remaining single-index text reads in each after
the edit; array/dict indexing like `caret_parts[i]`/`result[key]` is
unaffected — those are correctly `[T]`/`Dict` indexing, not text).

**Verified (PROVED, direct execution, before/after, all 3 copies):**
```
AFTER (all 3 copies) parse_line('*stopped,reason="café-hit",value="42"')
  -> cls=stopped reason=café-hit value=42
AFTER parse_line('^done,name="日本語",id="7"')
  -> cls=done name=日本語 id=7
AFTER parse_line('*stopped,frame={func="a—b",line="5"}')
  -> cls=stopped frame={func="a—b",line="5"}
AFTER parse_line('^done,reason="exited",code="0"')
  -> unchanged (regression guard)
```
No recursion in any of the fixed functions (plain `while` loops, same
shape as `convert_storage.spl`) — A/B'd anyway: **default engine and
`SIMPLE_EXECUTION_MODE=interpret` agree**, both correct, on the
`nogc_sync_mut` copy (representative of all 3, same functions).

Spec: `test/01_unit/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser_multibyte_spec.spl`
(4 cases, targets the `nogc_sync_mut` copy). Not run through
`bin/simple test` per the harness caveat.

## 5-9. Audited, no bug found (full-file read, not just top sites)

- **`src/lib/scv/structural_match.spl`** — the exact bug this campaign's
  survey originally found in `scv_find_char_pos` (char_at-walk bounded by
  byte-len) was **already fixed by another session** between the survey
  and this pass (`3bd6c52ef5b "fix(scv): make scv_find_char_pos
  byte-indexed to match its callers"`). Confirmed by reading the landed
  fix — now `s.index_of(ch)`, byte-consistent. No action needed.
- **`src/lib/gc_async_mut/pure/nn/serialization.spl`** (11/11 sites, full
  file read) — every site is either a fixed-ASCII-prefix strip
  (`"SHAPE:"`/`"DATA:"`/`"EPOCH:"`/`"LR:"`, always literal ASCII
  regardless of payload) or a byte-walk that reconstructs content via
  `result = result + s[i:i+1]` stepping `i` by exactly 1 every iteration
  (byte-identical reconstruction even for multi-byte content, same
  mechanism proved safe for `json.spl` in the original survey). No
  `char_at`, no single-index text access. No bug.
- **`src/lib/nogc_sync_mut/web_framework/session.spl`** (10/10 sites, full
  file read) — `dot_pos`/`eq_pos` from `.last_index_of`/`.index_of`
  (byte-consistent); remaining sites are fixed-offset type-tag prefix
  strips (`"i:"`/`"b:"`, 2-byte ASCII) or numeric-literal sign checks. No
  bug.
- **`src/os/services/llm/widget_eval.spl`** (7/7 sites + 1 single-index
  site newly checked) — `pi`/`close_idx`/`ci` all from `.index_of`. The
  one single-index site, `_count_indent`'s `line[i] == " "`, is
  bounded-safe despite being character-indexed: indentation counting only
  ever scans up to the first non-space character, which single-index
  access reaches correctly in the same order as byte-index would (ASCII
  spaces are always 1 char = 1 byte), and the loop returns immediately on
  the first non-space — the byte/char divergence is never actually
  reached. No bug.
- **`src/lib/nogc_async_mut/mcp/fileio_json.spl`** (9/9 sites) — same
  proven-safe byte-walk-with-ASCII-delimiter-detection pattern as
  `json.spl` in the original survey (`after[i:i+1]`/`rest[i:i+1]`
  stepping by 1 every iteration, comparing against ASCII quote/comma/brace
  literals). No `char_at`, no single-index text access. No bug.

## Landing

7 files changed: `convert_storage.spl` (fix), `gdb_mi_parser.spl` × 3
(fix), 2 new multi-byte specs. `structural_match.spl`,
`pure/nn/serialization.spl`, `web_framework/session.spl`,
`widget_eval.spl`, `mcp/fileio_json.spl` unchanged (no bug found, or
already fixed elsewhere). No gate/budget files touched.
