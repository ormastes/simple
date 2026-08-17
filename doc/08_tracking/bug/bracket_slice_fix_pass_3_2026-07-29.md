# Bracket-slice byte-index survey — fix pass 3 (2026-07-29)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Batch 3, widened hunt per the coordinator's pattern: files mixing bare
single-index `s[i]` (character-indexed) with a `.len()`/`.length()`-bounded
loop or index arithmetic from `index_of` over the SAME counter. Searched
via the exact-idiom signature `X[i].ord()` (a very high-confidence
fingerprint for this bug class: get a numeric value from a character at a
position, then use that position elsewhere as a byte offset) across
`src/`, plus targeted checks of remaining unaudited survey HIGH files and
parser/protocol files.

## 1. `src/lib/common/encoding/toml.spl` — FIXED (5 sites, severe: whole-document data loss)

TOML config parser. `_toml_char_at(s, i) = s[i].ord()` is the file's core
character-classification helper, called from every scanning loop, all
bounded by `.length()` (confirmed == `.len()`, i.e. BYTE length, not
character length). Plus 4 more independent single-index sites doing the
actual character-append (main string-value loop, key-parsing loop,
int-parsing loop, `toml_encode`'s re-escape loop) — found on a *second*
grep pass after fixing the helper; the first pass's 3-site count was not
exhaustive (same lesson as batch 2's `_replace_pairs` miss).

**Concrete pre-fix failure (PROVED, direct execution):**
```
toml_parse("a = \"café\"\nb = \"plain\"\n") -> 0 entries (should be 2)
toml_parse("greeting = \"日本語\"\nnum = 42\n") -> 1 entry, both values empty (should be 2, both correct)
toml_parse("name = \"ascii\"\nother = \"plain\"\n") -> 2 entries, both correct (pure ASCII control, unaffected)
```
Not a partial/local failure — one multi-byte value anywhere in the
document corrupted parsing of every entry after it.

**Fix:** `_toml_char_at` now returns `s.bytes()[i]` (a real byte value,
matching `.length()`'s byte semantics) instead of `s[i].ord()` (a Unicode
codepoint via character-indexed access). The 4 append sites switched from
single-index `s[i]` to byte-indexed 1-byte slices `s[i:i+1]`.

**Verified (PROVED, direct execution, full required character set):**
```
doc: a="café" b="中文" c="日本語" d="a—b" e="😀smile" f=42 g="tail"
-> 7/7 entries, all exact: café, 中文, 日本語, a—b, 😀smile, 42, tail
round-trip: toml_parse(toml_encode(entries)) -> same 2/2 entries, exact
  (includes the 😀 emoji, a 4-byte UTF-8 codepoint -- the most extreme
  case in the required set)
```

**A/B under `SIMPLE_EXECUTION_MODE=interpret` (no recursion in this file,
but checked per instruction anyway):** default engine gives all 7/7 exact
values above. Forced interpreter gives the right VALUES but with a
trailing `"` character appended to every multi-byte string (`café"`,
`中文"`, `日本語"`, `a—b"`, `😀smile"`) while pure-ASCII/numeric values
(`42`, `tail`) are unaffected. This is a genuine engine divergence, not a
logic error in the fix (the default engine is unambiguously correct) —
consistent with, and new evidence for,
`doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`.
Not investigated further (out of scope, per instruction). **`bin/simple
test` on the spec below will red** for this same reason — verify via
direct execution instead.

**Known follow-up, not fixed here (flagged, not silently absorbed):**
`_toml_char_at` now calls `.bytes()` (an O(n) full-string-to-array
conversion) on every invocation, and it's on the hot per-character scan
path (46 call sites across the file). Correct and fine for typical
KB-sized config files; a real optimization would thread a pre-computed
byte array through every caller instead — a larger refactor, out of scope
for a correctness pass.

Spec: `test/01_unit/lib/common/encoding/toml_multibyte_spec.spl` (3 cases:
full character-set parse, encode round-trip, ASCII regression guard).

## 2. `src/lib/nogc_sync_mut/mqtt/packet.spl` (+ 2 byte-identical mirrors: `nogc_async_mut/...`, `gc_async_mut/...`) — FIXED (encode: PROVED; decode: correct in isolation, blocked end-to-end by a separate pre-existing bug)

`mqtt_encode_string`'s own docstring says "Encode UTF-8 string" — MQTT
topic/payload strings are UTF-8 per spec. Same `X[i].ord()` bug, bounded
by `.length()`.

**Concrete pre-fix risk:** for any real multi-byte MQTT string, the
character-indexed cursor would exhaust the string's characters before
reaching the byte-length bound baked into the 2-byte length prefix already
written to the output.

**Fix (encode):** `text[i].ord()` → `text.bytes()[i]`.

**Verified (PROVED, direct execution):**
```
mqtt_encode_string("café") -> [0, 5, 99, 97, 102, 195, 169]
  (2-byte length prefix = 5 bytes; payload = exact UTF-8 bytes for café)
mqtt_encode_string("hi")   -> [0, 2, 104, 105]  (ASCII regression guard)
```

**Fix (decode, `mqtt_decode_string`):** also rewrote the byte→text
reconstruction from `byte_val.chr()` per byte (WRONG: treats each raw wire
byte as its own Unicode codepoint, producing mojibake for any multi-byte
character — verified directly: decoding café's wire bytes `[195,169]` via
`chr(195)+chr(169)` gives `"Ã©"`, not `"é"`) to collecting the raw bytes
and UTF-8-decoding them as a whole via
`text_from_codepoints(utf8_decode_all(raw_bytes))`.

**This exact decode logic is PROVED correct in isolation:**
`utf8_decode_all([99,97,102,195,169])` → codepoints `[99,97,102,233]` →
`text_from_codepoints(...)` → `"café"`, verified directly, standalone.

**INFERRED, not proved, for the full-module round-trip:** calling
`mqtt_decode_string` through the actual module gave `decoded=(caf, 7)`
(missing "é") instead of `"café"`. Root-caused (not guessed): this
module's OTHER functions (`mqtt_encode_remaining_length(length)` etc.)
have untyped parameters, which forces the **whole module** to fall back to
the interpreter at compile time (`HIR lowering error: Parameter 'length'
... requires explicit type annotation` → `JIT compilation failed for the
whole file`, confirmed by the compiler's own diagnostic output). My
standalone `utf8_decode_all`/`text_from_codepoints` test above did **not**
show this fallback message and ran under the default engine, correctly.
This is the same interpreter-engine divergence documented in
`test_harness_execution_divergence_2026-07-29.md`, now compounded by a
**second, separate, pre-existing defect** (missing type annotations
forcing interpreter fallback for this specific file) that guarantees this
module always hits the interpreter bug in its current state, regardless of
this fix. Neither the type-annotation gap nor the interpreter engine bug
was fixed in this pass (both out of scope — a codegen/interpreter fix and
a broader type-annotation sweep are both larger, separate tasks). The
decode fix is landed because it is provably correct (same logic verified
in isolation) and strictly better than the prior `.chr()`-per-byte code,
which was wrong for ASCII-adjacent Latin-1 range values too (any raw byte
128-255 was already silently wrong before this fix, not just multi-byte
sequences) — not because the full round-trip is demonstrated end-to-end
here.

Spec: `test/01_unit/lib/nogc_sync_mut/mqtt/packet_multibyte_spec.spl` (2
cases, encode direction only, matching what's provably verified).

## 3. `src/lib/nogc_sync_mut/kafka/serialization.spl` (+ 2 byte-identical mirrors: `nogc_async_mut/...`, `gc_async_mut/...`) — FIXED (encode + CRC32: PROVED; decode: correct in isolation, blocked end-to-end by a different separate pre-existing bug)

Same `X[idx].ord()` bug in `crc32_calculate` and `serialize_string`, plus
the same `.chr()`-per-byte reconstruction bug in `deserialize_string`.

**`crc32_calculate` is a correctness bug, not just a crash risk, even
where the old code didn't crash:** Kafka's real CRC32 is computed by the
broker over the actual wire bytes. A codepoint-based CRC (the old
`data[idx].ord()`) would silently disagree with the broker's byte-based
one for any non-ASCII key/value, independent of whether the character-vs-
byte-length mismatch happened to crash for a given input length.

**Fix:** `data[idx].ord()`/`value[idx].ord()` → `.bytes()[idx]` in
`crc32_calculate`/`serialize_string`; `deserialize_string` rewritten the
same way as `mqtt_decode_string` (collect raw bytes, then
`text_from_codepoints(utf8_decode_all(raw_bytes))` instead of
`byte_val.chr()` per byte).

**Verified (PROVED, direct execution):**
```
serialize_string("café") -> [0,0,0,5, 99,97,102,195,169]
  (4-byte big-endian length prefix = 5; exact UTF-8 payload bytes)
serialize_string("hi")   -> [0,0,0,2, 104,105]  (ASCII regression guard)
crc32_calculate("café") != crc32_calculate("hello")  (no crash, distinct)
```

**INFERRED, not proved, for `deserialize_string`'s round-trip:** calling
it after `serialize_string("café")` returned `""` instead of `"café"`.
Traced (not guessed) with temporary instrumentation: `bytes_to_int32`
decoded the 4-byte length prefix `[0,0,0,5]` as **40**, not 5 — a **10x**
error unrelated to text content entirely (this is the structural
length-prefix bytes, before any payload byte is touched). This reproduces
`5 -> 40 = 5 << 3`, matching the shape of this codebase's documented
`list`-indexing tag-shift defect family (`reference_list_get_returns_value_shifted_left_3` /
adjacent memory) — `deserialize_string`'s `bytes: list` parameter uses the
generic `list` type (not a typed `[i64]` array), and indexing it
(`bytes[offset]`) appears to hit the same corruption class. This is a
**separate, pre-existing bug that predates this fix and is unrelated to
multi-byte content** — it happens on the pure length-prefix bytes, so it
would have broken `deserialize_string` for any input, including 100%
ASCII, before this pass touched the file. Not fixed here (a `list`-type
indexing defect is a different, deeper, out-of-scope investigation). The
decode fix (byte-collection + UTF-8 decode) is landed on the same
"provably correct in isolation, strictly better than `.chr()`-per-byte"
basis as `mqtt_decode_string` above.

Spec: `test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl`
(3 cases: encode direction, CRC32 non-crash/distinctness, ASCII regression
guard — matching what's provably verified).

## Files checked this pass with no bug found

- `src/lib/nogc_sync_mut/http/headers.spl` — all bracket accesses are
  array indexing (`digits[i]`, `lines[j]`, `seen[s]`, etc.), no single-index
  text access.
- `src/lib/common/encoding/ini.spl` — same, array indexing only
  (`sections[j]`, `sections[si]`); does not use the `X[i].ord()` idiom.
- `src/app/dap/protocol.spl`, `src/lib/nogc_sync_mut/dap/protocol.spl`,
  `src/lib/nogc_sync_mut/lsp/parser_adapter.spl`,
  `src/compiler_rust/lib/std/src/mcp/simple_lang/parser.spl`,
  `src/app/md_lsp/md_lsp_handler.spl` — no single-index text access found.
- `src/lib/scv/maintenance.spl`, `src/app/portal/server.spl` — the
  bracket-index hits found are on `[u8]`/array receivers (byte-array
  comparisons against `N.to_u8()`, `items[i]`/`segments[i]` array copies),
  not text.
- `src/lib/common/encoding/protobuf_wire.spl`, `.../base58.spl`,
  `.../bencode.spl`, `src/compiler/10.frontend/parser_types_expr.spl` —
  all use the same `X[i].ord()` idiom but were **not** investigated deeper
  this pass (found via the systematic grep, deprioritized below Kafka/MQTT
  for real-world impact and time budget). Flagged for the next pass:
  `protobuf_wire.spl` already has an explicit ASCII-fast-path caveat
  comment acknowledging the limitation (lower priority); `base58.spl`
  operates over a fixed ASCII alphabet by design (likely low risk);
  `bencode.spl` (BitTorrent) and the compiler-internal parser file not yet
  assessed for real risk.

## Landing

10 files changed: `toml.spl` (fix), `mqtt/packet.spl` × 3 (fix),
`kafka/serialization.spl` × 3 (fix), 3 new multi-byte specs. No
gate/budget files touched.
