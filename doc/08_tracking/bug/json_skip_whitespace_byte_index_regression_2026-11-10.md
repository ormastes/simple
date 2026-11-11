# `json_skip_whitespace` byte-index regression: non-ASCII content corrupts every following token

Status: FIXED 2026-11-10 (release/1.0.0 Windows interpreter lane); symptom matches
the reopened family of `json_tokenizer_rejects_raw_non_ascii_strings_2026-07-29.md`.

## Symptom

`gh_json_roundtrip_spec.spl` failed on the Windows interpreter lane: example 1
(title containing raw `é`) died with
`force unwrap failed: expected Some or Ok, got Option::None` from
`json_value_parse_opt(bb_pr_to_gh_json(...))!`. Short JSON with non-ASCII
parsed fine; long JSON with non-ASCII failed; long pure-ASCII parsed fine.

## Cause

`json_skip_whitespace` had been converted (after the 2026-07-29 sentinel fix)
to a `byte_at` walk: it takes and returns a BYTE-space position.
`json_tokenize`'s main loop walks with 1-unit `substring` slices, which are
CHARACTER-indexed under the interpreter. The two index spaces agree on pure
ASCII and desynchronize by one position per multi-byte character. After the
first raw non-ASCII string token, whitespace was no longer skipped and object
keys fell apart into single-character INVALID tokens (`": "` became a STRING
token, etc.). When the non-ASCII sat near the end of the input, the closing
brace still resolved by luck, masking the desync — hence the
length-dependent symptom.

## Fix

Restored `json_skip_whitespace` to the documented 2026-07-29 pattern: 1-unit
`substring` walk with the empty-slice EOF sentinel, same index space as its
caller. Verification: `gh_json_roundtrip_spec` 3/3, plus devhub unit sweep
62/62 specs green on the Windows interpreter lane.

## Note for the compiler owners

The engine-divergence trap here (bracket slices are char-indexed under the
spec-lane interpreter but byte-indexed under compiled code, while `len()` is
bytes everywhere) keeps re-biting individual functions. A repo-wide audit of
`byte_at` positions returned to `substring` callers — or one canonical
text-cursor API — would be cheaper than per-function whack-a-mole.
