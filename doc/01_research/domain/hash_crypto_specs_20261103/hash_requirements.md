# Hash specification requirements

Status: requirements draft; execution and coverage UNMEASURED. Source identities,
rights and local extraction limitations are in [sources.md](sources.md).
The tables identify obligations, not completed tests. Boundary lengths are test
design deductions from specification branches, not quotations of published vectors.

## BLAKE3-256

Reference: pinned BLAKE3 paper, section 2, PDF pages 4–8 (printed pages match).
The tree combines 1024-byte chunks; compression consumes 64-byte blocks. Root
output is distinct from intermediate chaining values. Empty input remains a
valid root chunk. Keys, context strings and output lengths must follow the API
actually exported by each Simple owner; unsupported modes are scope gaps.

| ID | Source location | Required assertion / boundaries |
|---|---|---|
| REQ-HASH-BLAKE3-001 | 2.1, 2.2, 2.4; pp. 4–7 | Independent 32-byte digest for lengths 0, 1, 63, 64, 65, 1023, 1024, 1025; binary input containing 00/7f/80/ff. |
| REQ-HASH-BLAKE3-002 | 2.1, 2.5; pp. 4, 7 | Tree merge and incomplete right subtree: 2047/2048/2049 and 3072/4096/4097 bytes; compare published or independently generated digest. |
| REQ-HASH-BLAKE3-003 | 2.3; pp. 6–7 | Where exported, keyed hash and derive-key with the official key/context; assert exact independent outputs and malformed-key contract. No plain-hash substitute. |
| REQ-HASH-BLAKE3-004 | 2.6; p. 8 | Where exported, XOF 0/1/31/32/33/63/64/65-byte lengths and seek/block boundary; exact output prefix/content. |
| REQ-HASH-BLAKE3-005 | 5.1 incremental implementation discussion | Where exported, split updates around 64/1024-byte boundaries, empty update and finalization; exact independent output. API-specific repeated-finalize behavior needs its owner contract. |

Existing candidate: `test/01_unit/lib/common/crypto/blake3_kat_spec.spl`; separate
OS candidate `test/01_unit/os/crypto/blake3_kat_spec.spl`. Mere path existence does
not prove any row is satisfied. Worker must record exact scenario IDs and owner.
Upstream vector JSON uses a repeated 0..250 input pattern; do not substitute text
or a 0..255 pattern. Its longer output can provide the first 32 bytes for BLAKE3-256.

## XXH3-128

Reference: `xxhash_spec.md`, version 0.2.0 from pinned xxHash v0.8.3; headings
"Seed and Secret", short-input classes, medium input, and large input. Use
`xxhash.h` at the same pinned commit to resolve the reference API/oracle.

| ID | Source location | Required assertion / boundaries |
|---|---|---|
| REQ-HASH-XXH3-001 | Empty input; 1–3; 4–8; 9–16-byte headings | Exact both halves for lengths 0/1/3/4/8/9/16; seed 0, nonzero and full-width high-bit seed; binary bytes. |
| REQ-HASH-XXH3-002 | 17–128 and 129–240 headings | Both halves at 17/31/32/33/63/64/65/95/96/97/127/128/129/239/240/241. |
| REQ-HASH-XXH3-003 | Large input: blocks, stripes, last 64 bytes, finalization | Independent results around 64-byte stripe boundaries and secret-dependent block length. Default secret gives 1024-byte block; custom secret length changes it. Include one less/exact/one more and multi-block remainder. |
| REQ-HASH-XXH3-004 | Seed and Secret; reference `XXH3_SECRET_SIZE_MIN` | Custom secret 136/137/192 bytes where supported; reject shorter input through production validation rather than invoking upstream undefined/precondition-violating API. |
| REQ-HASH-XXH3-005 | XXH128 canonical reference API | Assert digest serialization byte order and both halves; 64-bit equality alone cannot establish 128-bit correctness. |
| REQ-HASH-XXH3-006 | Reference streaming/reset APIs; production API contract | Where exported, split updates around short/stripe/block boundaries, empty updates and reset with full-width seed; exact independent 128-bit result and seed preservation. Streaming availability is a repository API requirement, not a new digest algorithm. |

Production owner identified by worker: `src/lib/common/crypto/xxh3.spl`,
`_k_xxh3_128` family. `test/01_unit/lib/common/crypto/xxhash_kat_spec.spl` is only
a candidate inventory path: distinguish XXH32/64 from actual XXH3-128 tests.
Reference C execution produces independent expected values, never Simple coverage.

## gxHash

The author-linked PDF `gxhash-article.pdf` is revision 1, November 2023, 21 pages.
It is historical design context; use pinned `gxhash-mod.rs` implementation plus
README and MIT license for revision-specific reference behavior. This upstream
HEAD includes evolving size classes; first confirm
which revision/algorithm the production owner claims. Do not silently update
Simple to match a different hash family or version. Tests must pin matching
reference output and identify architecture-dependent backend.

Historical paper anchors: section 4.1 (pipe width) and 4.2 (compression), page 9;
4.3 (finalization) and 4.4.1–4.4.3 (alignment, looping, padding), pages 10–11.
These motivate width, block/tail, alignment and padding tests, but current
reference size thresholds come from the pinned code. `tests::is_stable` in
`gxhash-mod.rs` contains published gxhash64 vectors across seeds/lengths and
additional output-width examples: published source vectors are not executed
Simple evidence. Worker investigation currently reports no owned production
gxHash implementation (SCVN-H03); retain BLOCKED until that owner is established.

| ID | Source location | Required assertion / boundaries |
|---|---|---|
| REQ-HASH-GXHASH-001 | `gxhash32`, `gxhash64`, `gxhash128`; `compress_all` | Assert the exposed width(s), empty input, seed zero/nonzero/negative, binary 00/7f/80/ff; independent known output. |
| REQ-HASH-GXHASH-002 | `compress_all`, `compress_upto_128` | Exact digests for 0/1/15/16/17/31/32/33/63/64/65/127/128/129 to expose partial padding, overlap and lane merges. |
| REQ-HASH-GXHASH-003 | `compress_large`, `compress_lanes`, `compress_16` | Revision-matched boundaries 511/512/513 and 2047/2048/2049, plus multiple loop iterations/remainders. These are current pinned upstream branches, not asserted production branches. |
| REQ-HASH-GXHASH-004 | platform partial-load implementation + production owner | Memory alignment/page-edge paths only where reachable in the actual owner; record hardware prerequisites and exact backend. Do not count an upstream SIMD branch against a pure-Simple denominator. |

Missing oracle, unsupported API, unexercised production branch or revision mismatch
stays an explicit gap. Do not manufacture malformed-input cases for an arbitrary
byte-string hash whose API has no malformed byte-string domain.

## Supplemental repository evidence contracts

These IDs supplement standard-derived obligations without renumbering them.

| ID | Scope | Required assertion |
|---|---|---|
| REQ-HASH-BLAKE3-ADAPTER-001 | Repository byte adapter | Preserve exact input byte values and length across the adapter, including 00/7f/80/ff; this does not prove production BLAKE3 hashes all those bytes correctly. |
| REQ-HASH-EVIDENCE-001 | Typed oracle controls | Corrupted digest evidence and missing required evidence must fail closed; a capture or adapter-only pass cannot satisfy algorithm conformance. |
