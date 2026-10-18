# Feature Expert: BLAKE3 / XXH3 / gzip (pure Simple)

## What this is
Pure-Simple content hashes and the gzip/DEFLATE codec, verified against the
official specifications' own vectors. Plan:
`doc/03_plan/lib/crypto/hash_gzip_hardening_2026-10-18.md`.

| Need | Use | Never |
|---|---|---|
| immutable artifact id, distributed cache object, content verification | `std.common.crypto.blake3` (`blake3_text` -> 64-hex digest of text, `blake3_hash`, `blake3_keyed_hash`, `blake3_derive_key`, `blake3_hash_xof`; `blake3_hex` only hex-encodes bytes, it does not hash) | XXH3 (not collision-resistant) |
| fast local fingerprint, AST/TLDR cache index key | `std.common.crypto.xxh3` (`xxh3_128`, `xxh3_128_hex`, `xxh3_64`, `_seeded`, `_with_secret` — 64-bit returns `[u64]`, `[]` on a short secret) | anything adversary-controlled |
| gzip file / HTTP gzip | `std.nogc_sync_mut.compression.gzip` (`gzip_decompress` decodes every member with `inflate_member`) | raw `inflate` for a gzip member (it tolerates a missing BFINAL for sync-flush) |

## Consumers (wired 2026-10-18)
| Site | Hash | Spec |
|---|---|---|
| `src/compiler/80.driver/cache/package_tldr_metadata.spl` `package_tldr_interface_key_v1` / `package_tldr_action_key_v1` (TLDR archive identity, `/v2` tags) | BLAKE3-256 (`blake3_text`) | `test/01_unit/compiler/cache/package_tldr_metadata_spec.spl` |
| `src/compiler/80.driver/driver_parse_shard_hash.spl` `driver_parse_shard_hash` (parse/HIR shard owner index and claim-marker name) | XXH3-64 of the path, `>> 1` | `test/01_unit/compiler/driver/parse_shard_hash_xxh3_spec.spl` |

Not moved, on purpose: content-body digests (`cas_put`/`cas_get`, the frontend
parse (AST) cache key `frontend_parse_cache_key`, HIR cache body/keys). They use
the C-accelerated SHA-256; pure-Simple hashing of whole files would regress the
cache hit path (interpreter: BLAKE3 ~0.9 s, XXH3 ~0.15 s per 64 KiB, SHA-256 ~0).
HIR cache keys are also pinned to 64 hex across the archive/lease modules, so
XXH3-128 (32 hex) cannot go there without a schema change.

Measured (seed `bin/local/seed_simple`, sha256 prefix 9c45d2bf601ab93e):
| Case | Before | After |
|---|---|---|
| shard hash, 2000 calls on a 58-byte path, interpreter / JIT | djb2 1.49 s / 0.14 s | XXH3-64 1.11 s / 0.12 s |
| 200 short (~300 B) keys, interpreter / JIT | SHA-256 0.11 s / 0.33 s | BLAKE3 1.14 s / 0.28 s |

## Specs (all vectors copied verbatim from the official sources)
| Spec | Source | Scenarios |
|---|---|---|
| `test/01_unit/lib/common/crypto/blake3_kat_spec.spl` | BLAKE3 `test_vectors.json` (all 35 lengths, XOF, keyed, derive_key) | 58 |
| `test/01_unit/lib/common/crypto/xxh3_kat_spec.spl` | xxHash `tests/sanity_test_vectors.h` (315 rows, 4 tables) | 14 |
| `test/01_unit/lib/nogc_sync_mut/compression/gzip_rfc1951_1952_spec.spl` | RFC 1951 §3.2, RFC 1952 §2, host `gzip -9n` known answers | 112 |

xxHash sanity input: `g = 2654435761; buf[i] = g >> 56; g *= 0x9E3779B185EBCA8D`;
withSecret rows use `buf[7 .. 154)` (147 bytes) as the secret, seed 0.

## How to verify on a host without a pure-Simple CLI
`bin/simple test` on the Rust seed prints no results (silent green). Use
`<seed> run <spec>` and read `SPEC FILE VERDICT ... executed=N failed=0`.
Coverage: `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<p> <seed> run <spec>`
writes line hits, function call counts and a `decisions` table
(true/false counts per `if`/`while`) — branch coverage = every decision
seen both ways. Tail expressions and continuation lines are never recorded.

## Landmines (all found in this lane)
- Seed JIT: `.to_u8()`/`push` on an untyped value is mis-encoded (value >> 3);
  type the params/arrays. `doc/08_tracking/bug/seed_jit_untyped_to_u8_push_double_untag_2026-10-18.md`.
- Seed JIT: unwrapping a `u64?` (`.unwrap()` or untyped `?? d`) yields a pointer-like value;
  return `[u64]` instead. `doc/08_tracking/bug/seed_jit_optional_u64_unwrap_2026-10-18.md`.
- Seed interpreter: an unannotated `val x = f() ^ g()` of extern-backed u64
  calls becomes signed; annotate `: u64`.
  `doc/08_tracking/bug/seed_interp_u64_inference_signed_2026-10-18.md`.
- A `use` inside a fn body demotes the whole module to the interpreter under
  JIT (`[jit-fallback] unresolved external symbol`). Module-level `use` only.
- Interpreter cost is dominated by fn calls in hot loops: BLAKE3 went
  0.66 s -> 0.22 s (64 B x200) by inlining rotations onto scalar locals.
- Check the ENCODER against an independent decoder (host `gzip -dc`), not only our own
  inflate: a same-path round trip hid the >65535-byte stored-block LEN truncation.
- Do not fabricate KATs (`fabricated_blake2s_65_byte_kat_2026-08-04.md`).
