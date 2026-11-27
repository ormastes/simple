# slang pure tokenizer: vocab parse mixes char length with byte substring offsets

Status: verification-pending
Date: 2026-11-16

## Symptom
`generate_spec` "truncates at a stop string spanning tokens" failed (5/6) on the seed. The
decoded text was just "\n": the vocab piece for "▁" (id 4) decoded to "", so a stop
string taken from the text was empty and nothing could span tokens.

## Root cause
`pure_tokenizer_from_json` / `_quoted_item` (`src/lib/gc_async_mut/slang/model_executor/pure/tokenizer.spl`)
sliced lines with `substring()` (byte offsets) using `_char_len()` (codepoint count) as the end.
For any line containing a multi-byte codepoint ("▁" is 3 bytes) the end offset fell short, the
id text became empty, `parse_i64` failed and the vocab entry was silently dropped
(`pieces[id] == ""`). Stop handling (`stop.spl`, `generate.spl`) was already byte-consistent.

## Fix
Use `byte_len()` for those substring ends. Regression coverage: `generate_spec.spl`
(6/6), `stop_spec.spl` (7/7). `tokenizer_spec.spl` improves 2/6 -> 5/6 on the seed; its
remaining failure (`function skip not found`, "matches the reference ids") is unrelated.

## Not covered
Native (non-interpreted) run not verified.
