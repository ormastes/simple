# lib encoding/parsing churn hunt — quadratic concat & re-derived state

## Status: FIXED (2026-10-03) — all items below verified seed-run; one related finding left OPEN (hex_slice, TLS lane)

Library perf/memory bug hunt over `src/lib/common/encoding/`, `src/lib/common/sdn/`,
`src/lib/common/json/`, and `src/lib/common/crypto/sha256_core.spl` (Rust seed
runtime, diagnostic labeling: seed-run). Font files (`font_registry.spl`,
`sfnt*.spl`) left untouched per the pinned glyph contract. `gc_async_mut/gpu/engine2d`
and `skia` excluded (other lane).

Every fix is content-equivalent (same output, less churn); each carries new
content-equivalence regression cases in the nearest unit spec.

## Fixed item 1 — SDN `_sdn_split_lines`: O(line²) per line

**File:** `src/lib/common/sdn/parser.spl:163`

Built each line with `cur = cur + c` per character. A single 800 KB line cost
~3×10^11 byte copies before parse — a CPU/mem-DoS on any trusted-`parse`
caller of large single-line documents (`parse_untrusted`'s 1 MiB cap did not
help; the churn was inside the line splitter, not bounded by it).

**Fix:** emit `s.slice(start, i)` at each `'\n'` (one byte-scan, no per-char
materialisation). Verified with a probe: 200 KB and 800 KB single-line
documents now parse in well under a second (old code: effectively never).

Regression cases: `test/01_unit/lib/common/parsers_sdn_coverage_spec.spl`
("churn-regression (perf-fix equivalence)": 10 000-byte single-line value,
200-line mapping, escaped quoted strings).

## Fixed item 2 — SDN `_sdn_unescape`: O(n²) per escaped string

**File:** `src/lib/common/sdn/parser.spl:512`

`out = out + ch` per character on any string containing a backslash.

**Fix:** accumulate parts, `join("")` once. Unknown escapes still preserved
verbatim (`\q` → `\q`); regression case pins this.

## Fixed item 3 — JSON tokenizer: double `join("")` per string token

**File:** `src/lib/common/json/parser.spl:250`

`str_parts.join("")` was computed twice per string token (validate + push),
re-copying every token's bytes.

**Fix:** join once into a local, validate and push that. Regression cases in
`test/01_unit/lib/common/parsers_json_core_spec.spl` ("string-token
churn-regression"): 800-escape long token (exact length + prefix), non-ASCII
token, invalid-escape rejection in a long token.

## Fixed item 4 — bencode decode: `s.bytes()` re-derived per byte read

**File:** `src/lib/common/encoding/bencode.spl:88` (`_benc_char_at`)

Every single-byte read in every decode loop materialised the FULL input byte
array, making one decode O(n²) in byte-array copies. The text-taking helper is
replaced by `_benc_byte_at(b: [u8], i)` and each decode function
(`_benc_decode_int_at/_str_at/_value_at/_list_at/_dict_at`,
`_benc_text_lt`) hoists `data.bytes()` once.

## Fixed item 5 — bencode insertion sorts: full array rebuild per shift

**File:** `src/lib/common/encoding/bencode.spl` (`_benc_sort_keys`,
`_benc_sort_pairs`)

Each insertion-sort shift rebuilt both arrays element-by-element: O(n) fresh
elements per shift, O(n³) total copies for a reverse-sorted dict.

**Fix:** in-place index-assignment shift (same insertion sort, same output).
Stability (strict `<`) unchanged.

## Fixed item 6 — bencode encode: per-item text concat

**File:** `src/lib/common/encoding/bencode.spl` (`bencode_encode_list`,
`bencode_encode_dict`, `bencode_encode` BDict case)

`result = result + item` per entry — O(total_bytes²). Now parts arrays +
`join("")` once.

Regression cases: `test/01_unit/lib/common/encoding/bencode_spec.spl`
("Bencode churn-regression"): hand-computed BEP 3 dict encoding, 40-item list
frame length, 360-byte string decode equivalence, nested dict decode →
re-encode round-trip.

## OPEN — TLS `hex_slice`: O(n²) per-char concat, TLS-lane file

**File:** `src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl:113`

`result = result + hex_digit(hex_nibble(...))` per hex char. Called on the TLS
record hot path (`tls/record.spl:51`, `tls/handshake.spl:43`,
`tls/cipher.spl` key splits) with payload-sized inputs — a 16 KB record
payload costs ~10^8 char copies per record. Left OPEN because the file belongs
to the active TLS lane; fix is mechanical (parts + `join`, preserving the
current lowercase-normalising behavior — a plain `text.slice` would NOT be
equivalent since the decoder re-encodes case). Suggest the TLS lane pick this
up.

## Clean areas (read, no confirmed bugs)

- `utf8.spl` / `utf16.spl` / `utf32.spl` — already single-pass or
  differential-oracle refactored; decode loops append directly.
- `base64.spl` / `base64url` — already `[u8]`-accumulate + single convert;
  exact-size preallocation in `_base64url_encode_raw`.
- `sha256_core.spl` — block-local schedule, push-growth bounded by 64; pad
  target arithmetic uses i64 throughout.
- `sdn/parser.spl` `parse_untrusted` — pre-parse depth/entry/indent/size caps
  already present and asserted by specs.
- `bencode` decode — i64 magnitude guards on integer and length accumulation
  (no wrap), `substring` slice for payloads (no per-char copy).
- `json_number_is_valid` / `json_skip_whitespace` — byte-walk, ASCII-exact.
- `text_ops.spl`, `codec.spl`, `msgpack.spl` (bounds-guarded),
  `cbor/bson/protobuf_wire` (dedicated guard specs exist and pass).

## Verification (all seed-run, `--mode=interpreter`, SIMPLE_TIMEOUT_SECONDS=0)

- `bin/simple check --syntax-only` — bencode.spl, sdn/parser.spl,
  json/parser.spl: PASS.
- bencode_spec 47/47, bencode_multibyte 2/2, bencode_offset_guard 6/6,
  parsers_sdn_coverage 85/85 (incl. 3 new), sdn_coverage 71/71, sdn_spans
  15/15, sdn_named_table 6/6, roundtrip 6/6, sdn_block_sequence 7/7,
  sdn_sequence_duplicate_key 3/3, sdn_2_complete 15/15,
  parsers_json_core 101/101 (incl. 3 new).
- Pre-existing failure unrelated to this change:
  `test/01_unit/app/sdn_spec.spl` fails with a spec-file lex error
  ("Unclosed backtick atom literal") — the file itself does not compile; it
  does not exercise the library parser.
