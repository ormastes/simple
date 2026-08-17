# Bracket-slice byte/char index campaign — Pass 6 (2026-07-29)

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Scope (coordinator assignment): the last named deferral — bencode's **decode**
path (`src/lib/common/encoding/bencode.spl`). Encode side was already fixed in
pass 4 (03267955f6ed).

## PROVED

- **Root cause**: `_benc_char_at(s, i) -> i64` read via `s[i].ord()`.
  Single-index text access (`s[i]`, no colon) is **character**-indexed on
  this engine (independently reconfirmed this pass via `.substring()` probe
  and earlier campaign evidence: `"café"[3]` is the whole 2-byte `"é"`, not a
  byte). Every one of the 5 mutually-recursive decode functions
  (`_benc_decode_int_at`, `_benc_decode_str_at`, `_benc_decode_value_at`,
  `_benc_decode_list_at`, `_benc_decode_dict_at`) bounds its `pos`/`cur` loop
  by `data.length()` (byte length) and feeds those same byte offsets into
  `data.substring(cur, cur+slen)` (byte-indexed, confirmed by probe). Mixing
  the two access modes through the shared `_benc_char_at` helper corrupted
  parsing on any input with a multi-byte character before the target offset.
  A single fixed-point fix, `s.bytes()[i]`, corrects all 5 sites because none
  of them bypass this helper with direct indexing (confirmed by grep: no
  other `data[pos]`-shaped single-index access exists in the decode path).

- **Vacuity confirmed**: swapping back in the original `s[i].ord()` against
  the pass's own fixture reproduces `DECODE_ERROR` (total parse failure, not
  a subtle corruption) — the bug is real and severe on any realistic
  torrent-shaped document containing non-ASCII strings.

- **Fixture** (torrent-shaped, hand-specified by the coordinator): a dict
  with a multi-byte key (`café`) mapped to a multi-byte value (`中/日本語`),
  a nested list mixing an ASCII item (`a`), a 4-byte-UTF-8 emoji
  (`😀`) and an integer (`42`), plus plain-ASCII pairs
  (`name`→`test`, `num`→`123`). Reference bytes computed independently via a
  from-scratch python3 bencode encoder (not this repo's code, not from
  memory — `scratchpad/bencode_ref.py`), byte-sorted key order per the
  bencode dict spec:
  ```
  d5:café13:中/日本語4:listl1:a4:😀i42ee4:name4:test3:numi123ee
  ```
  68 bytes total.

- **Direct-decode, both engines, post-fix, against the Result-free
  `_benc_decode_value_at` API**: identical, correct output under the
  deployed default engine and under `SIMPLE_EXECUTION_MODE=interpret` —
  `ok=true consumed=68`, all 4 dict pairs correct (including the multi-byte
  key/value pair and the nested list's 3 items, emoji included). **No engine
  divergence** for the core decode logic — unlike `base58_decode` (pass 5),
  this fix does not expose a reversed-polarity (or any) engine disagreement.

- **Round-trip (headline), both engines**: constructed the same structure as
  a `BencodeValue.BDict(...)` literal, ran it through the already-fixed
  `bencode_encode` (pass 4), decoded the result back through
  `_benc_decode_value_at`, and compared. Under both the default engine and
  `SIMPLE_EXECUTION_MODE=interpret`:
  ```
  encoded_len=68 (expect 68)
  encoded=d5:café13:中/日本語4:listl1:a4:😀i42ee4:name4:test3:numi123ee
  decode_ok=true consumed=68
  roundtrip_pairs=4 (expect 4)
  rt[0] café=str:中/日本語
  rt[1] list=list_len:3
  rt[2] name=str:test
  rt[3] num=int:123
  ```
  Byte-exact match against the independently-derived reference in both
  directions (encode output == reference bytes; decode of that output ==
  original structure), identical under both engines.

- **Recursion + call-boundary landmine (pass-1 finding) — checked, already
  safe**: every recursive call in the decode path
  (`_benc_decode_list_at` → `_benc_decode_value_at(data, cur)` at the former
  line 414; `_benc_decode_dict_at` → `_benc_decode_str_at(data, cur)` /
  `_benc_decode_value_at(data, cur)` at the former lines 446/454) already
  passes a plain pre-extracted local (`cur`), never an inline-computed
  expression, as the recursive argument. No change needed; verified by
  reading each call site.

- **Re-grep of the whole file for residual single-index bugs**: the only
  other single-index (`s[i]`, no colon) sites left in the file are in the
  **encode** path already reviewed/fixed in pass 4
  (`_benc_text_to_bytes`, already bounded by character count with an
  explanatory comment; `bencode_encode_bytes`'s `prefix[i]` walks a
  guaranteed-ASCII `"<digits>:"` prefix where char count == byte count).
  Neither is in scope for or affected by this pass's decode fix.

## INFERRED / documented, not fixed (separate, non-blocking finding)

- **`bencode_decode_value`'s `Result<BencodeValue, BencodeError>`-wrapped
  public API fails under `SIMPLE_EXECUTION_MODE=interpret`** with
  `error: semantic: unknown class Result`, even for trivial ASCII input
  (`"i42e"`) — isolated via a minimal reproduction with no multi-byte
  content, proving this is unrelated to the byte/char index bug fixed this
  pass. It is an interpreter-mode limitation in `Result`-class resolution
  for this call shape, not a decode-correctness bug. Workaround used
  throughout this pass's verification: call the lower-level,
  `Result`-free `_benc_decode_value_at(data, pos) -> _BencDecResult` (a
  plain struct) directly. Not fixed — out of scope for the byte/char index
  campaign; left as a distinct, separately-filed-worthy interpreter
  limitation for the engine lanes.

## Fix

`src/lib/common/encoding/bencode.spl`, `_benc_char_at`:
```
fn _benc_char_at(s: text, i: i64) -> i64:
    s.bytes()[i]
```
(was `s[i].ord()`; full rationale in the function's docstring, updated
in-place with the same reasoning as this doc's PROVED section).

## Campaign status

This closes the last named deferral of the bracket-slice byte/char index
campaign. Remaining open items are the two engine-specific bugs that stay
with the engine investigation lanes (not this campaign):
- `base58_decode` carry-propagation reversed-polarity bug (pass 5: default
  engine wrong, interpreter correct).
- kafka `bytes_to_int32` tag-box `.get(i)` corruption (pass 3, `list.get(i)`
  returning `value<<3`).
