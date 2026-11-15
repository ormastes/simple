# Selected-font validation hashed at ~22 KB/s on the interpreter lane

**Status:** FIXED (2026-11-15)
**Area:** `src/lib/common/encoding/font_registry.spl`, `_validate_selected_font_asset_with_digest`

## Symptom

`test/01_unit/lib/common/text_layout/font_renderer_selected_registration_spec.spl`
timed out alone. It had already been split out of `font_renderer_spec`, and it
was still killed past the 900 s worker budget. Each of the 16 pinned faces
(~52 MB in total) is hashed about four times:
- malformed-bytes registration;
- the refusal-reason recompute;
- the real registration;
- `try_load_registered_identity` → `_load_selected_bytes`.

## Cause

`bin/simple test` runs with an interpreter runtime mode. On that lane the
validator took `bytes_to_hex(sha256_bytes(_u8_blob_to_i64_array(blob)))`, a
pure-Simple SHA-256. That route was a crash workaround from 2026-07-26 (deep
interpreter recursion in the u8-tail implementation). It predates
`0dc896b1907` (2026-10-25), which routed `sha256_u8_hex` through the runtime
accelerator `rt_tls13_sha256`. Under the interpreter that accelerator returns
the correct 32 bytes. Nothing re-pointed the font validator at it.

## Fix

`_font_interp_digest_hex(blob)` calls `sha256_u8_native_hex_or_empty` first. On
"" (no provider, or a non-32-byte sentinel), it falls back to the old
`sha256_bytes` route. A missing accelerator is therefore slower, never a
different verdict. The freestanding forced-native route and the precomputed
file-digest fast path are unchanged.

## Evidence

Seed: `cargo-target-webrender-vk/release/simple`. Load average was about 10–12.

| measurement | before | after |
|---|---|---|
| `validate_selected_font_asset` on NotoSansMono (1,708,408 B), in-process | 77,155 ms | 11 ms |
| registration spec (16 faces, 1 row), wall | > 900 s (killed) | 86 s, 1/1 pass |
| registration spec maxrss | n/a | 245,172 KB |

The registration row still asserts what it did before: every malformed blob is
refused, every exact blob registers, and every identity reloads.

The four-hashes-per-face redundancy is left as is. At native speed it costs
milliseconds.
