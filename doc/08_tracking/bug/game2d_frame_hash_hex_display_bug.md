# `frame_hash_hex` formatter renders decimal where hex was intended

**Priority:** low (display only — FNV-1a binary value is correct, fixture stability holds)
**Filed:** 2026-04-25
**Component:** `src/lib/nogc_sync_mut/game2d/backend/frame_hash.spl`
**Discovered by:** game2d-framework SStack Phase 5b / Phase 7

## Description

`frame_hash_hex(buf)` is the human-readable formatter wrapping `frame_hash(buf)`.
The binary FNV-1a hash itself (`frame_hash`) is correct and byte-stable —
fixture comparison via the binary value passes 11/11 in
`test/system/game2d_golden_spec.spl`.

The `_hex` formatter, however, renders the `u64` as **decimal** rather than
hex. Display-only bug: the function name promises hex, the output is decimal.

## Evidence

- `src/lib/nogc_sync_mut/game2d/backend/frame_hash.spl` — `frame_hash_hex` body.
- `.sstack/game2d-framework/state.md` `### 7-verify-rerun-2 W4` item 7: "`frame_hash_hex` decimal-vs-hex display bug (display only; FNV-1a binary value via `frame_hash` is unaffected, fixture stability holds)".
- Fixture content: `test/fixtures/game2d_golden_hello_720p.hash = 0x253edd45a462bc15` (the hex literal IS the documented contract — the formatter just emits it as decimal).

## Suggested fix direction

Replace the formatting call with the `0x{:016x}` (or Simple-equivalent
`hex_pad_16`) format spec. Add a unit test asserting `frame_hash_hex(0x253edd45a462bc15)`
returns `"0x253edd45a462bc15"`.
