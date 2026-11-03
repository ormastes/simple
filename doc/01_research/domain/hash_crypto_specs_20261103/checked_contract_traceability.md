# Checked API and profile traceability gaps

Status: source/fixture audit only; all referenced Simple checks remain
AUTHORED_UNRUN unless a separate execution receipt says otherwise. This note
adds missing distinctions, not another inventory or replacement requirement set.

| Pending contract | Primary anchor and independent oracle | Remaining evidence boundary |
|---|---|---|
| SQLCipher REQ-CIPHER-RESERVE-001/002, test-first `2e20a20da72` | Pinned v4.6.1 `sqlcipher_codec_ctx_reserve_setup` (source lines 717–735) adds IV and enabled HMAC sizes, rounds to cipher block. The locked IV16/HMAC64 profile yields 80. `sqlcipher_page_cipher` authenticates before decryption. | Reserve0/79/81 rejection and authenticated reserve80 admission are repository profile constraints, not universal SQLite or every SQLCipher configuration. Bad-tag precedence/error codes are repository contracts. Preserve a plaintext SQLite reserve0 positive control. |
| ChaCha checked encryption `81fd968be8d9b5053b0b28c9c6ed0c4895e63e17` | RFC 8439 2.8 (p.20): 32-byte key, 12-byte nonce. Section 2.8.2 is the independent exact ciphertext/tag oracle. Existing shared and OS input-shape specs cover published-vector success and adjacent/empty invalid widths. | Result variants, error strings, SCV translation and dynamic ABI -1 are repository choices. Existing dynamic argument guards do not exercise the new defensive Err branch. Stable requirement links/manuals and qualified execution remain owed. |
| WebSocket mask Result migration | Reuse RFC 6455 5.3/5.7 and the reviewed network addendum. Published Hello frame is a wire oracle, not proof of random-source strength. | Strong entropy and fresh-per-frame requirements survive any Result signature change. No successful fallback on entropy failure; exact error type and caller propagation are repository contracts requiring actual caller/failure-path evidence. |
| gxHash design, width selection pending | Pinned Cargo.toml reports version 4.0.0; platform modules, seed packing and partial-load semantics belong to the same `5e00a497...` revision. Historical paper revision 1 (November 2023) remains design context only. | No production implementation/coverage claim. User-selected output width and version compatibility must precede implementation. SIMD is not inferred as a requirement. Use published `tests::is_stable` vectors or separately recorded execution of the compatible upstream oracle. |
| BLAKE3 true ff-byte cases | Existing published input pattern i modulo 251 never emits ff. Pinned upstream reference implementation `f55849f8...` can generate independent outputs for 00/7f/80/ff and boundary repeats. | Generated upstream-reference outputs must be labeled differential oracles, not official published corpus entries. Record source, harness, compiler and output hashes, mode/key/context and exact inputs; adapter-only evidence does not prove hash compression of ff. |

SQLCipher fixture provenance: the lane's generator at
`test/fixtures/database/sqlcipher4/gen_reserve_fixtures.ps1` uses .NET
PBKDF2/AES-256-CBC/NoPadding/HMAC; the worker reports independent Python HMAC
checks. These are generated interoperability fixtures, not official published
vectors. HMAC validation alone does not establish decrypted header correctness;
the production open/admission assertions remain required. Test path:
`test/02_integration/app/devhub/messenger/sqlcipher_reserve_admission_spec.spl`.

ChaCha shape tests live under `test/01_unit/{lib,os}/crypto/` in
`chacha20_poly1305_input_shape_spec.spl`. Existing SCV guards make the new
defensive error translation unreachable under current inputs; report that
branch honestly rather than relabeling guard tests as its execution proof.

WebSocket lane `websocket_mask_entropy_spec.spl` supplies the exact RFC Hello
frame, invalid entropy-width and controlled Err cases, zero-mask acceptance,
server bypass, wrappers and fragments. A zero-valued mask is legal within the
32-bit domain when selected by strong entropy; nonzero/unique samples are not
the normative condition. RFC 6455 5.1 distinguishes mandatory client masking
from prohibited server masking. Provider-failure/no-send execution and generated
manual evidence are still pending; controlled Err tests do not prove them.

gxHash draft audit compared all 22 rows / 88 gxhash64 constants in the worker's
`gxhash_published_vectors.sdn` to pinned `tests::is_stable`: exact match, with
input (31*i+7) modulo 256 and seed order 0,42,-1,i64::MIN. This validates the
transcription only. Full 128-bit boundary oracles and lengths 511/512/513 and
2047/2048/2049 remain missing; low-64 equality cannot establish 128-bit results.

## ECDSA SPKI follow-up source

RFC 5480 (March 2009) 2.1.1, printed p.4, identifies id-ecPublicKey and
requires curve parameters; 2.1.1.1 gives secp256r1 on p.6; 2.2 on p.7 maps
ECPoint octets to BIT STRING and requires support for uncompressed 04 points.
Compressed 02/03 support is optional; other point tags must be rejected.
A fixed 91-byte uncompressed P-256 API is a repository scope restriction.
Rejecting a changed algorithm/curve OID follows that restriction and the
algorithm identity; do not merely strip a fixed prefix. Zero unused bits
follows octet-aligned point mapping with DER, rather than an explicit
RFC 5480 instruction naming the DER unused-bit count byte. Test an independent
valid SPKI and mutated header fields; this is separate from ECDSA math KATs.

## Newly pinned oracle-support originals

Existing sources were reused. These seven new originals are private cache
artifacts under `C:/dev/p3new/hash-coverage-20261103/spec-cache`; upstream code
keeps its MIT (gxHash) or Apache-2.0 option (BLAKE3) license context from the
existing manifests. RFC 5480 retains the IETF copyright notice. This document
is an original summary, not a full transcription. Hashes were verified once.

| Original | SHA-256 | Retrieved UTC |
|---|---|---|
| [gxhash-platform-mod.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/gxhash/platform/mod.rs) | 85e15369b410c4ae88c9e1e3f5a613eb663a69c5f858c1da59e05e09d176cdac | 2026-11-03T03:35:20.0983685Z |
| [gxhash-platform-x86.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/gxhash/platform/x86.rs) | 456f737acec6c31d9b4a5c52f9724f91242005b7f3d232285068bae734a90441 | 2026-11-03T03:35:20.4110953Z |
| [gxhash-platform-arm.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/gxhash/platform/arm.rs) | 885f50ba7e79bb5840a7efb4c03e0bee5aa9717a778143144749997ce0ebd471 | 2026-11-03T03:35:20.6747108Z |
| [gxhash-Cargo.toml](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/Cargo.toml) | 02b1233673ea56fc883f37979207e86c9743c7f5a9623dbd74136a98d6035f9c | 2026-11-03T03:35:20.9408673Z |
| [gxhash-hasher.rs](https://raw.githubusercontent.com/ogxd/gxhash/5e00a497289d1c2f0ae07e5f956654c77f1cfc09/src/hasher.rs) | cbfd42ed51528f372b3d00dd39977825c4055cb97299b41fcca2d6343a087776 | 2026-11-03T03:35:21.1894887Z |
| [blake3-reference_impl.rs](https://raw.githubusercontent.com/BLAKE3-team/BLAKE3/f55849f89cd85083c1c9daa2c5de20766f309c00/reference_impl/reference_impl.rs) | 6e89a18be72e3c4d838644e1796e04d896cb4a16bd7bb803d4380d7a363fbfd2 | 2026-11-03T03:35:21.4566798Z |
| [rfc5480.txt](https://www.rfc-editor.org/rfc/rfc5480.txt) | 593bf29fd0da2ff8b903c3ebf1c9d189a770039159e2ba46a0c3b91355037f26 | 2026-11-03T03:36:35.5016747Z |
