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

## Consumers (wired 2026-10-18; AST key 2026-10-19)
| Site | Hash | Spec |
|---|---|---|
| `src/compiler/80.driver/cache/package_tldr_metadata.spl` `package_tldr_interface_key_v1` / `package_tldr_action_key_v1` (TLDR archive identity, `/v2` tags) | BLAKE3-256 (`blake3_text`) | `test/01_unit/compiler/cache/package_tldr_metadata_spec.spl` |
| `src/compiler/80.driver/driver_parse_shard_hash.spl` `driver_parse_shard_hash` (parse/HIR shard owner index and claim-marker name) | XXH3-64 of the path, `>> 1` | `test/01_unit/compiler/driver/parse_shard_hash_xxh3_spec.spl` |
| `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl` `h1_decode_content_encoding` (HTTP `Content-Encoding` gzip/x-gzip, zlib-or-raw deflate; zstd/br rejected; post-decode 50 MiB cap) | gzip/deflate decoders | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_content_encoding_spec.spl` |
| `src/compiler/10.frontend/frontend.spl` private parse (AST) cache key, `frontend_parse_cache_key`, and the M2->M3 `.fpc` binding in `driver_aot_native_output.spl` / `cache/phase_compatibility_admission.spl` | XXH3-128 via the runtime accelerator `xxh3_128_text` (`std.nogc_sync_mut.sffi.crypto`, extern `rt_xxh3_128_text`) | `test/01_unit/compiler/frontend/supplied_source_cache_key_spec.spl` |
| `src/os/services/nvfs/core/compression.spl` LZ4 algo=1 extents (`lz4_compress_block`/`lz4_decompress_block`, `[u32 len \| block]`, raw fallback to algo=0 when not smaller; legacy len+4 tagged-copy still decodes) | LZ4 block (not a hash) | `test/01_unit/lib/fs_driver/nvfs_compression_spec.spl` |

`rt_xxh3_128_text(data: text) -> text` is the XXH3-128 accelerator: C twin in
`src/runtime/runtime_native.c` (scalar port, 32-bit-limb multiply for MSVC;
checked against all 45 seed-0 XXH128 sanity rows), Rust lane
`xxhash_rust::xxh3::xxh3_128` in `runtime/src/value/sffi/hash/xxhash.rs`,
interpreter wrapper in `interpreter_extern/crypto.rs`. It is VALUE-ABI (boxed
text in, text out), not a text-ABI `(ptr,len)` extern and not `[u8]`-returning
(the shape behind doc/08_tracking/bug/jit_rt_tls13_sha256_returns_empty_2026-08-05.md). `xxh3_128_text` falls back to pure-Simple `xxh3_128_hex` on
any non-32-hex answer and records it (`xxh3_128_text_fallback_used`).

The private parse key changed from 64-hex SHA-256 to 32-hex XXH3-128; old
`.fpc` files are never named again and age out through the LRU cap. The shared
parse CAS (`SIMPLE_SHARED_PARSE_CAS_ROOT`) keeps its SHA-256 source identity
(cross-host, target-receipted), and `frontend.spl` now computes that SHA only
when a shared root is configured. XXH3 is not collision-resistant: that is
accepted for the per-scope private directory only.

Not moved, on purpose: `cas_put`/`cas_get` and HIR cache body/keys (64 hex is
pinned across the archive/lease modules; XXH3-128 needs a schema bump there),
and the receipt digests in the target-receipted parse path (`source_digest`,
`preprocessed_digest`), which are SHA-256 identities other code verifies.
`parse_full_frontend_preprocessed_with_scope` returns the parser-input TEXT,
and only the target-receipted caller hashes it into `preprocessed_digest`, so
an ordinary parse pays no whole-file SHA-256 at all. Pinned by
`target_cfg_receipt_v1_spec` ("binds the preprocessed digest ...").

Measured (seed `bin/local/seed_simple`, sha256 prefix 9c45d2bf601ab93e):
| Case | Before | After |
|---|---|---|
| shard hash, 2000 calls on a 58-byte path, interpreter / JIT | djb2 1.49 s / 0.14 s | XXH3-64 1.11 s / 0.12 s |
| 200 short (~300 B) keys, interpreter / JIT | SHA-256 0.11 s / 0.33 s | BLAKE3 1.14 s / 0.28 s |
| AST key over 400 compiler files x5 (27 MB), JIT / interpreter (seed `5bdd376460541de9`) | SHA-256 76 ms / 206 ms | XXH3-128 1.35 ms / 9.5 ms |

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

## Block-size limits (frame encoders)

- Zstd: Block_Maximum_Size is 128 KiB and the block header size field is 21 bits.
  `zstd_compress_frame` splits input into <=128 KiB raw/RLE blocks (RLE per block when
  its bytes are identical); Last_Block=1 only on the final block.
- LZ4: the frame BD byte declares a 64 KiB max block, and the decoder rejects larger
  blocks. `lz4_compress_frame` emits independent <=64 KiB blocks (each compressed or
  stored raw, with a per-block checksum when enabled).
- Specs: `zstd_frame_variants_spec.spl` and `lz4_spec.spl` (mirrored under `test/unit/`).

## RSAES-PKCS1-v1_5 padding randomness (2026-10-19)
`std.common.crypto.rsa_pkcs1` type-2 PS is random nonzero bytes from
`csprng_bytes` (`std.common.aes.utilities`, `rt_random_i64`), rejection-sampled;
entropy failure returns `[]`. Do not use `entropy_platform_bytes` there yet:
`rt_entropy_fill` is unbacked in the seed. The padding helper is private; the
spec observes it via `rsa_pkcs1_public_encrypt` with e=1 and an all-0xFF
modulus (ciphertext == padded block, no RSA-2048 modexp). Spec:
`test/01_unit/lib/crypto/rsa_pkcs1_padding_spec.spl`.
- Lookup tables (AES S-box / inverse S-box): build ONCE per top-level operation
  (key expansion, `_gctr`, public block encrypt/decrypt) with the existing push
  builder and pass it down as a parameter. No module-level globals (native
  codegen segfault) and no `[u8]` literal tables (native corruption), see
  `doc/03_plan/lib/crypto/all_cipher_compress_algorithm_gate.md`. The old
  per-byte `_aes_sbox()` rebuilt 256 entries on every lookup. Measured
  (4 KiB AES-256-GCM): interp 14.0 -> 10.3 s, jit 0.28 -> 0.21 s, jit RSS
  174 -> 103 MB. `crc32.update_byte/update_u32` are compiler-intrinsic pattern
  wrappers with no library callers; left as is.

## zstd decoder: Predefined_Mode and Repeat_Mode sequence tables (2026-10-19)
- `zstd_seq.spl::_zstd_parse_sequence_tables` no longer blanket-rejects Repeat (3) or
  all-Predefined (0,0,0); those were placeholders pinned by `zstd_sequence_header_spec`
  and `zstd_single_sequence_compress_spec`, not guards against a real defect. Default
  LL/ML/OF distributions (36/53/29 symbols, AL 6/6/5) match RFC 8878 3.1.1.3.2.2.
- Table history is threaded per frame in `zstd_dict.spl` (`sequence_table_history`);
  an RLE-mode table is stored in history as a 1-entry table_log 0 table so a later
  Repeat reuses it. `sequence_history_established` (dictionary or an earlier sequence
  block) makes Repeat on a first block a CorruptStream error, since the default history
  is the predefined tables and would otherwise decode silently wrong.
- Real fixtures: `test/01_unit/lib/common/zstd_predefined_repeat_modes_spec.spl`
  (host `zstd` 1.5.5; repeat frame needs `--zstd=wlog=10` for small blocks, `-19`).
