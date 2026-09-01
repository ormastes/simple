# UTF-8 reference coverage — 2026-08-26

Production owner: `src/lib/common/encoding/utf8.spl`

Retained final command used the lightweight source-instrumented runner with
`test/01_unit/lib/common/encoding/utf8_spec.spl`.

| Cycle | Spec | Examples | Branch | Line |
|---|---|---:|---:|---:|
| 1 | focused validation | 26/26 | 4/23 (17%) | 37/145 (25%) |
| 2 | broad reference | 52/52 | 30/44 (68%) | 110/145 (75%) |
| 3 | expanded malformed/boundary matrix | 58/58 | 41/42 (97%) | 115/139 (82%) |

Two unreachable zero-progress checks were removed from decode loops because an
in-bounds `utf8_decode_one` always consumes at least one byte. Added tests cover
negative offsets, invalid numeric payloads, malformed continuations, overlong
3/4-byte encodings, surrogates, U+10FFFF overflow, invalid codepoint byte
lengths, and mixed-width text construction.

The remaining branch is documented in
`doc/08_tracking/bug/utf8_text_invalid_guard_blocks_branch_closure_2026-08-26.md`.
No 100% claim is made.
