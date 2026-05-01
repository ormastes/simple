# Agent Task Breakdown — `common_compression_framework`

This task split assumes multiple spawned workers operating in parallel while preserving the pure-Simple constraint. Each worker owns code/tests in its lane, rebases frequently, and does not fork new Rust/runtime feature work.

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
