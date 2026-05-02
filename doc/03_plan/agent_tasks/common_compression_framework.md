# Agent Task Breakdown — `common_compression_framework`

**Encoder seed (uncompressed-only) LANDED 2026-05-01** — full LZ77+Huffman compressed encoder deferred. `brotli_encode_uncompressed([u8]) -> [u8]` lives in `src/lib/nogc_sync_mut/compression/brotli/encoder.spl` with `bit_writer.spl` mirror; round-trip verified through existing decoder via `test/unit/lib/nogc_sync_mut/compression/brotli_encoder_seed_spec.spl` (5/5 specs).

This task split assumes multiple spawned workers operating in parallel while preserving the pure-Simple constraint. Each worker owns code/tests in its lane, rebases frequently, and does not fork new Rust/runtime feature work.

## Current Status (2026-05-01)

Latest verify report (`doc/09_report/verify_common_compression_framework.md`) is STATUS=FAIL with **5 hard failures and 5 warnings** (down from 7/3 after Wave 1: F flipped lzma2:330 FAIL→WARN, N flipped zstd:1265 FAIL→WARN; M kept zstd:704 FAIL but added test-seam + Kraft bug-doc cross-reference).

### Wave 1 outcomes (2026-05-01)

- **F (LZMA2 decode) — LANDED partial**: pure-Simple LZMA range coder + LZMA2 chunk decoder interoperate with host `xz -z --check=crc32` at default LCLPPB=3/0/2 (props 0x5D); 22/22 specs PASS in `test/unit/lib/common/lzma2_range_coded_spec.spl` and `xz_lzma2_spec.spl`. Other LCLPPB tuples explicitly rejected via `UnsupportedFeature`. Closure tracked in FR `doc/08_tracking/feature_request/lzma2_full_lclppb_2026-05-01.md`. Side note: F caught a `0u32 - (x>>31)` interpreter wrap edge case while implementing the range coder; worked around in the lzma2 hot path, **no bug doc filed yet** — Wave 2 should chase or file.
- **M (Zstd FSE Huffman-weight) — TEST SEAM LANDED, KRAFT BUG FILED**: `_zstd_parse_fse_compressed_weights` is wired and dispatched; `test/unit/lib/common/zstd_fse_weights_spec.spl` (5 cases, PASS 2026-05-01) pins the typed-error surface. Decoder mis-decodes every real-world host-zstd FSE Huffman tree (Kraft completion fails on 5/5 fixtures); bug `doc/08_tracking/bug/bug_zstd_fse_huffman_weight_kraft_2026-05-01.md` filed (multi-day, OPEN). zstd:704 stays FAIL until the Kraft completion path is fixed.
- **N (Zstd dictionary frame parser) — LANDED partial**: pure-Simple decode parses RFC 8478 §6 dictionary blobs (magic `0xEC30A437`, Dictionary_ID match, HUF + FSE_Offsets/Match_Lengths/Literals_Lengths entropy tables, 3 recommended offsets, content as LZ77 prefix) and seeds per-frame decoder state. `test/unit/lib/common/zstd_dictionary_spec.spl` (8 cases, PASS 2026-05-01) covers parser positives, malformed-magic / id-mismatch / truncated-after-HUF / truncated-recommended-offsets / zero-rep-offset rejections, plus a Raw_Block frame round-trip referencing a dictionary by id. **End-to-end Compressed_Block decode that consumes the dictionary's seeded entropy tables is DEFERRED** because real-world dict HUF sections use the FSE-compressed weight path blocked by M's Kraft bug; spec uses the direct-weight path (header_byte ≥ 128) to side-step it.
- **C (StaticCompressionCache) — LANDED**: `static_file_compression_cache_integration_2026-05-01` wired into `nogc_async_mut/http_server` static_file path; FR closed.

### Outstanding FAIL/WARN surface (5/5)

- **FAIL** `src/lib/common/compress/mod.spl:49` — façade still rejects Zstd encode levels other than `3`, dictionaries for all codecs, and `checksum=false` for XZ/LZMA2 encode.
- **FAIL** `src/lib/common/compress/zstd.spl:324` — compressed-block decode still rejects non-RLE sequence tables. **[2026-05-01 W6 audit: cited line is stale — `_zstd_parse_single_sequence_table` (zstd.spl:367) already handles modes 0/1/2/3; the original line-324 stub `_zstd_parse_rle_sequence_tables` (zstd.spl:352) is unreachable dead code. The deeper FAIL on the live FSE-state path could not be empirically re-measured because of a brand-new compiler regression — `Value::UInt` missing method dispatch — that broke EVERY zstd spec including W5-E's previously 6/6 PASS `zstd_fse_weights_spec.spl`. Tracked at `doc/08_tracking/bug/interpreter_uint_method_dispatch_2026-05-01.md`. Status remains FAIL conservatively.]**
- **FAIL** `src/lib/common/compress/zstd.spl:704` — FSE-compressed Huffman-weight decode mis-decodes real-world fixtures (M's Kraft bug, OPEN multi-day).
- **FAIL** `doc/02_requirements/feature/common_compression_framework.md:30` — REQ-030 still overstates forced-tier parity closure.
- **FAIL** `doc/02_requirements/nfr/common_compression_framework.md:11` — NFR-011 still overstates end-to-end verification closure.
- **WARN** `src/lib/common/compress/zstd.spl:1265` — dictionary parser landed; end-to-end dict-driven Compressed_Block decode deferred behind M's Kraft bug.
- **WARN** `src/lib/common/compress/lzma2.spl:330` — LCLPPB=3/0/2 only; full-LCLPPB closure tracked in FR.
- **WARN** `src/lib/common/compress/zstd.spl:1` — implementation is large/multi-responsibility (maintenance risk, not a defect).
- **WARN** `doc/01_research/local/common_compression_framework.md:1` — research artifacts describe original full-scope target, not current state.
- **WARN** `test/unit/lib/common/zstd_frame_variants_spec.spl:1` — repeated runs stalled after first 4 passing cases; lane cannot claim a clean current PASS.

### Outstanding work

- Zstd encoder levels `!=3`, dictionaries for all codecs, `checksum=false` XZ/LZMA2 (façade option enforcement at mod.spl:49).
- FSE Huffman-weight Kraft completion (M's bug — multi-day, blocks zstd:704 FAIL flip + N's end-to-end dict spec).
- Non-RLE sequence-table compressed-block decode (zstd.spl:324).
- Full-LCLPPB LZMA2 (FR).
- REQ-030 / NFR-011 doc closure once the codec gaps above land.

## Shared constraints for every worker

- Stay inside `.spl` implementation and test surfaces
- Do not reintroduce subset/phased behavior
- Treat `common.compress` as the single shared implementation owner
- Preserve `CompressionCodec` and add behavior through the checked APIs and option enforcement already planned
- Coordinate fixture names and helper seams to avoid duplicate codec logic

## Spawned worker assignments

### Agent A: Shared infrastructure and SIMD helper seam

- Extract shared byte-kernel helpers for match extension, literal copy, overlap-safe match copy, CRC32, and XXH32
- Provide scalar oracle implementations and pure-Simple AVX2/NEON specializations
- Expose forced-tier entrypoints so specs can call scalar, AVX2, and NEON directly
- Remove duplicate helper logic from codec-local paths where practical
- Deliver helper-focused unit tests and parity fixtures

### Agent B: Façade semantics and checked API enforcement

- Finalize `common.compress` option validation and dispatch rules
- Enforce `block_mode`, `level`, `checksum`, `content_size`, `dictionary_bytes`, and `dictionary_id` semantics
- Keep `compress_bytes` and `encoder_finish` as fail-fast wrappers over checked variants
- Ensure typed `CompressionError` selection is consistent across codecs
- Deliver façade-level specs for success and failure behavior

### Agent C: LZ4 completion

- Complete pure-Simple LZ4 block and frame encode/decode
- Implement frame flags, block checksums, content checksum, content size, and multi-block framing
- Rework encode-side match finding onto shared helpers where it materially reduces duplication
- Validate host-generated frames and host-tool decode interoperability for emitted frames
- Deliver LZ4 corruption and truncation coverage

### Agent D: Zstd decode completion

- Finish decoder handling for normal host-generated frames
- Cover frame-header variants, window/content-size validation, dictionary id parsing, raw/RLE/compressed blocks, repeated FSE tables, compressed Huffman weights, treeless literals, and 4-stream literals
- Support multi-block and multi-frame decode
- Align decode hot paths with shared scalar/SIMD helpers
- Deliver host-fixture decode coverage and corruption matrix cases

### Agent E: Zstd encode completion and kernel adapter unification

- Build the pure-Simple Zstd encoder with block splitting, sequence generation, literal compression, FSE/HUF emission, checksum emission, and content-size emission
- Implement framed dictionary support using `dictionary_bytes` plus `dictionary_id`
- Replace `src/os/kernel/loader/zstd_decompress.spl` internals with a thin adapter over `common.compress`
- Preserve the kernel adapter’s legacy `Result<[u8], text>` contract through explicit error translation
- Deliver host `zstd` interoperability coverage and kernel parity specs

### Agent F: XZ/LZMA2 decode completion

- Replace the uncompressed-chunk subset with full LZMA2 chunk decode
- Support `.xz` block/index/footer validation, CRC verification, multi-block streams, and concatenated streams
- Fail non-LZMA2 filter chains explicitly
- Align copy/checksum hot paths with shared helpers
- Deliver decode fixtures and full corruption coverage

### Agent G: XZ/LZMA2 encode completion

- Emit canonical `.xz` streams using the LZMA2-only filter chain
- Implement real LZMA2 compression rather than uncompressed passthrough chunks
- Ensure content structure is compatible with host `xz`
- Coordinate container metadata and CRC behavior with Agent F
- Deliver host decode interoperability coverage for generated streams

### Agent H: Spec harness, fixtures, and forced-tier parity

- Build deterministic fixture generators and/or checked-in fixtures for small, medium, large, repetitive, incompressible, and mixed payloads
- Add forced-tier parity tests that directly call scalar, AVX2, and NEON helper paths
- Add codec-output parity tests proving helper-tier changes do not affect compressed or decompressed bytes
- Maintain shared corruption matrices and expected typed-error assertions

### Agent I: Integration, verification, and stabilization

- Merge overlapping helper/codec changes without reintroducing duplicate paths
- Run focused compression tests, full `bin/simple test`, `bin/simple build lint`, core runtime smoke, and MCP native smoke if required by touched paths
- Run `$verify` and fix any coverage, stub, or documentation drift failures
- Record any remaining concrete bugs only if they are outside the full pure-Simple scope and cannot be finished in the same change

## Dependency order

1. Agent A and Agent B start first because helper seams and option semantics constrain the codec work.
2. Agent C, Agent D, Agent F, and Agent H can proceed once the shared helper contracts are stable.
3. Agent E depends on Agent D for decode parity and Agent B for dictionary semantics.
4. Agent G depends on Agent F for container validation rules.
5. Agent I starts integration as soon as the first codec lane merges and owns final verification.

## Required handoffs

- Agent A publishes helper APIs, forced-tier hooks, and expected scalar oracle behavior.
- Agent B publishes the canonical option-validation matrix used by all codec workers.
- Agents C through G publish fixture inventories and typed-error expectations to Agent H.
- Agent E publishes the kernel adapter translation table to Agent I.
- Agent I owns the final merge checklist and verification sign-off.

## Definition of done

- No codec remains subset-only
- No duplicate standalone kernel Zstd engine remains
- Shared helpers back codec hot paths with forced scalar/AVX2/NEON coverage
- System specs cover round-trip, interoperability, corruption, checked failures, and adapter parity for the full target
