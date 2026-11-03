# BLAKE3 branch-coverage gap plan — 2026-11-03

Status: AUTHORED_UNRUN / BRANCH_UNMEASURED. No admitted source-matched runtime was available to the coverage coordinator. No seed, bootstrap, test execution, docgen success, or 99% coverage claim is made. Production source is unchanged.

Scope: `src/lib/common/crypto/blake3.spl`. Separate `src/os/crypto/blake3.spl` is not included in this owner's denominator and needs its own expanded KAT/mode matrix. The canonical IO facade is `src/lib/nogc_sync_mut/io/crypto_sffi.spl`; the app IO FFI backend is not exercised or credited.

Official PDF: BLAKE3-specs ac784c9f22a48327782f042ec2f4d8126b3b1744, SHA256 ce179e62f29a6e43ec1ac2fe62b5e063a18632cf936c430d1373bfa0b81fb349. Algorithm sections 2.2–2.6 specify compression, flags, tree shape and output. Published vector source: BLAKE3 f55849f89cd85083c1c9daa2c5de20766f309c00/test_vectors/test_vectors.json, SHA256 dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624. The campaign specification notes are `doc/01_research/domain/hash_crypto_specs_20261103/hash_requirements.md` (separate docs lane).

| Requirement | Existing evidence source | Added spec and rationale |
|---|---|---|
| REQ-HASH-BLAKE3-001: mode separation across blocks/chunks/tree | `test/01_unit/lib/common/crypto/blake3_kat_spec.spl`: hash 0,1,63,64,65,1023,1024,1025 and larger trees; keyed/derive 0,1,64,65,1024,1025,2049,8193 | Unit `blake3_boundary_gap_spec`: keyed/derive 1023; system `blake3_published_modes_spec`: keyed/derive 63 and 3073 (fourth chunk partial, tree fold under domain flags). No duplicate plain KAT padding. |
| REQ-HASH-BLAKE3-002: XOF counter and exact truncation | Existing 131-byte official XOF for 0,1024,1025,3073, plus prefix and zero-output checks | Unit gap: official 65-byte input output truncated to 1,63,64,65 bytes. Exact independent prefix, not implementation self-comparison. |
| REQ-HASH-BLAKE3-003: API invalid-input contract | Existing 31/33-byte key rejection and zero XOF | Unit gap: empty key rejection before key-word loads; negative XOF length returns no bytes. This is repo API behavior, not a PDF-mandated error representation. |
| REQ-HASH-BLAKE3-004: real caller and adapter byte integrity | Existing wrapper test checks only first byte of 65-byte legacy digest, empty text | Integration `blake3_adapter_spec`: all 32 legacy digest bytes; actual canonical IO facade with embedded NUL from official one-byte input. Unit hex rendering checks 00/7f/80/ff. |
| REQ-HASH-BLAKE3-005: fail-closed typed oracle | Existing KATs assert equality directly | System gap: closed canonical digest node exact expected value, positive control, deliberately corrupted observation and absent-node rejection. |

All spec basenames resolve under the corresponding `test/01_unit/lib/common/crypto`, `test/02_integration/lib/crypto`, or `test/03_system/lib/crypto` directory. Manuals mirror these paths below `doc/06_spec`; they contain exact spec hashes, vector artifact hash, steps, scenario titles, and folded source. They are authored, not generated or execution evidence.

Branch inventory targets (not coverage measurements): partial/full block branch; empty chunk correction; first/nonfirst block flags; zero/nonzero chunk count; parent merge entered/not entered and repeated; final stack fold; XOF early return and output iteration; key acceptance/rejection; adapter empty/nonempty loops. Compiler-generated branches and zero-hit functions must be included by the coordinator's actual mapping. Static path reasoning is not a numerator or denominator. No unreachable exclusions have been approved.

Remaining gaps: official input repeats bytes 0..250, so it includes 00/7f/80 but never ff. The new ff renderer check does NOT prove hash compression of ff. An independently pinned reference vector containing ff is still required. No streaming API exists here; do not invent streaming coverage. No keyed/derive XOF API exists. Context strings beyond the published context and huge counter high bits remain unmeasured. OS owner expansion remains outstanding.

Execution gate: qualify a source-matched Pure Simple runtime; run native specs with actual-run receipts and fail-closed stub guard; run spipe-docgen and require actual zero stubs; run coverage inventory selftest including uncalled branches; then collect per-owner/backend numerator and denominator with all zero-hit sites. Goal >=99% branches is unmet until measured. Sidecar lanes N/A; integration owner /root; final reviewer /root/astra_phase3_review. No parallel edits to production owner.
