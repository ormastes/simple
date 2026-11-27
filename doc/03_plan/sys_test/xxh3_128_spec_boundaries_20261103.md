# XXH3-128 specification boundary campaign — 2026-11-03

Status: AUTHORED_UNRUN; branch coverage UNMEASURED. Target: 99% branches per implementation/backend/target. Neither numerator nor denominator is available. No admitted pure-Simple runtime exists for this lane; no bootstrap/seed fallback, native production execution, scorer or docgen run was attempted. No zero-stub claim.

## Production and oracle ownership

Production baseline b03ea2b2ae3730d9dbcfd0d1d4fe0ae682fea868: `src/lib/common/crypto/xxh3.spl` owns kernels; `src/lib/common/hash/xxh3.spl` owns public typed wrappers and streaming. Both contain 64/128-bit behavior. Whole-file denominators must retain 64-bit branches; do not silently call them XXH3-128-only. No production source changes.

Official upstream is Markdown/reference code, not an official PDF. xxHash v0.8.3 revision e626a72bc2321cd320e953a0ccf1584cad60f363:

- [Specification](https://github.com/Cyan4973/xxHash/blob/e626a72bc2321cd320e953a0ccf1584cad60f363/doc/xxhash_spec.md), text version 0.2.0 (2023-06-29), SHA-256 `61c47af338b2feefcc7621700ef6b941bcf9b1dd33899c503f68cb797e7ef333`.
- [Reference header](https://github.com/Cyan4973/xxHash/blob/e626a72bc2321cd320e953a0ccf1584cad60f363/xxhash.h), SHA-256 `17973c0dc49d9854ca26caa191f0e12f7a424b68858d9a78de3860d959d85e4b`; BSD-2-Clause.
- Independent oracle compiled with clang, `XXH_STATIC_LINKING_ONLY` and `XXH_IMPLEMENTATION`; calls `XXH3_128bits_withSecret`, `XXH3_128bits_withSeed`, `XXH3_128bits`. This does not execute Simple production code.
- Private artifacts `C:/dev/p3new/hash-coverage-20261103/spec-cache/xxh3-vector-oracle.c`, SHA-256 `bdfab455d6b9cbce84120ed0d80e0d0cae1daa0a624027b75f92e34e26f5b912`; `xxh3-vectors.csv`, SHA-256 `fdc20c545df0fb60b3bc1c8573318c543c1f79506277570c98821d19851cb574`.

Reproduce using message byte `[0,127,128,255][i mod 4]`, secret byte `(13*i+5) mod 256`, the row lengths below, and seed `0xffffffffffffffff`. Expected constants are retained in specs. Oracle evidence class: executed independent-reference-vector. Production proof class: AUTHORED_UNRUN.

## Requirements and specification mapping

Canonical IDs are defined in `doc/01_research/domain/hash_crypto_specs_20261103/hash_requirements.md`: 001 short inputs; 002 medium inputs; 003 large inputs; 004 secret validity and exact outputs; 005 serialization; 006 streaming/reset and seed preservation. Shared mapping agreed with the specification owner; mixed boundary scenarios cite each applicable ID. This lane adds missing cases, not complete satisfaction of every canonical row.

| Requirement | Official section/local contract | Existing tests and gap | New coverage intent |
|---|---|---|---|
| REQ-HASH-XXH3-004 / REQ-HASH-XXH3-003 | Seed and Secret; large-input Steps 2–4 | `xxh3_kat_spec.spl` minimum secret checks only result length; reference vectors use 192-byte secrets | Unit 136/137-byte secrets at 0,4,240,241,575,576,577,1152,1153 input bytes; system exact 136-byte secret at 576 |
| REQ-HASH-XXH3-001 / REQ-HASH-XXH3-002 / REQ-HASH-XXH3-003 | Small/medium XXH3-128; seed-derived secret | Existing sanity/affine vectors broadly cover length classes | Unit binary high-bit seed at 0,2,7,15,159,160,191,192,223,224,239,240,241,255,256,257,1023,1024,1025,2048 |
| REQ-HASH-XXH3-004 | Minimum secret precondition; local fail-closed API | Existing empty/135-byte secrets rejected at one input size | Unit secret lengths 0,1,64,135 crossed with inputs 0,4,241,577; system public wrapper rejects 135-byte secret |
| REQ-HASH-XXH3-006 | Header streaming/reset/digest API; specified digest equivalence | `common/hash/xxh3_spec.spl` mostly compares to same-owner one-shot; reset seed zero | Integration independent digests at 240,241,1024,1025,2048; varied chunk sizes; empty updates; maximum seed survives reset; typed public wrapper |
| REQ-HASH-XXH3-005 | Overview low64/high64; canonical output | Existing empty/abc/sanity hex vectors | System binary 00/7f/80/ff exact words and high-word-first hex |

## Executable/manual pairs

- Unit `test/01_unit/lib/common/crypto/xxh3_128_spec_boundaries_spec.spl`: 3 scenarios; 18 secret vectors, 20 seed vectors, 16 rejection combinations.
- Integration `test/02_integration/lib/common/hash/xxh3_128_stream_contract_spec.spl`: 3 scenarios; independent streaming checkpoints; 2048-byte message at widths 1,63,64,65,255,256,257; reset and public wrapper.
- System `test/03_system/lib/hash/xxh3_128_published_contract_spec.spl`: 3 primary scenarios for binary canonical representation, minimum secret acceptance, invalid secret rejection.
- Each path has its `.md` mirror under `doc/06_spec/`, labeled authored/unrun with executable SHA-256 and folded source. These are source counts, not executed counts.

## Branch and verification plan

136/137-byte secrets yield nine stripes per 576-byte block. 575/576/577 and 1152/1153 target last-stripe/full-block scramble decisions; 137 changes secret-tail offsets. 240/241 targets direct seed mixing versus derived secrets; 159/160 and 191/192 target medium rounds. Streaming crosses 256-byte buffers and 1024-byte blocks, observes digest then appends, and resets. These are intended branch stimuli, not measured hits. No branch is declared unreachable.

Use existing `scripts/check/check-hash-algos-coverage.shs` after admitted runtime and never-called-function denominator selftest pass. Explicitly scope both production owners and existing 64/128 suites plus new specs. Retain zero-hit branches and measured denominator; separate backends and never use oracle C coverage as Simple coverage. A per-128-only scope must explicitly identify shared versus 64-bit-only functions and retain exclusions transparently.

Run admitted native runner with `--native-backend=llvm --assert-ran --no-cache --no-db --no-session-daemon --sequential --keep-artifacts`, pin producer/runtime identity; use separate Cranelift evidence. Then run `simple spipe-docgen <spec> --output doc/06_spec --no-index`, inspect readable primary steps/folded matrices and require genuine zero-stub results. Do not infer capture files from comments: captures are planned; assertions provide the actual oracle once executed.

No custom-secret streaming constructor is exposed, so none is invented. Invalid secret lengths never enter upstream C; empty-array rejection is the local Simple contract, not an upstream digest.

Merge owner: root. Review: root/Astra phase 3. Sidecar lanes: N/A. No unrelated source, vendor code or shared bug database edits.


## Coverage re-audit and default-scope repair — 2026-11-03

Source baseline: 4c1c754912e498f91f11a63a4d7f1c873bfdbd23, current release at
this bounded audit. Existing XXH3 additions are already landed through PR6075:
`6d87c5351a6` (vectors/specs) and `2a187727695` (canonical requirement alignment).
The production owners are unchanged from those additions; no algorithm repair
or duplicate vector suite is warranted by this review.

**99% is not measured.** Numerator, instrumented denominator and zero-hit
inventory are unavailable for both pure-Simple LLVM and Cranelift targets and
for the self-hosted interpreter. No coverage is borrowed from AES, upstream C,
the runtime text bridge, or any other implementation. Current source hashes:

- `src/lib/common/crypto/xxh3.spl`: SHA-256
  `840ce9cb15892f66c6ff14fc3837cd32ff2b523d611cf1d78fbc102e3f31635e`.
- `src/lib/common/hash/xxh3.spl`: SHA-256
  `a7e25139229e6d35a978167579077b46323561c2ac62835b667250d4d59ecc14`.

The companion `xxh3_128_source_decisions_20261103.sdn` records 35 lexical
if/elif/while statements in the kernel owner and 13 in the wrapper/streaming
owner, including function names, source lines and conditions. **These 48
source rows are not an instrumented denominator or a zero-hit report.** They
include 64-bit-only and shared functions and cannot establish execution,
short-circuit condition coverage, optimized native mapping or branch counts.

The existing coverage gate's default scope omitted `common/hash/xxh3.spl`,
and its default driving list omitted the existing public/streaming suite and
the three newly landed XXH3 specs. This made a default gate result insufficient
to describe both XXH3 owners even if the selected kernel rows passed. The gate
now includes the public owner and those four suites. No coverage exclusions,
thresholds, metrics, probes, timeout settings or production algorithms change.

Source decision stimuli already authored:

| Owner decisions | Existing stimulus |
|---|---|
| `_core128`, `_len17to128_128`, `_len129to240_128` | Existing official KAT/reference length classes; new binary seeded intermediate round boundaries |
| `_k_xxh3_128_seeded`, `_custom_secret`, `_secret_for`, public seeded dispatch | Seed zero/nonzero/high-bit and input 240/241 in existing and landed suites |
| `_hash_long_acc` final stripe/full-block scramble | 575/576/577 and 1152/1153 for minimum secrets; default-secret 1023/1024/1025 and multiblock vectors |
| `_k_xxh3_128_with_secret` | Rejected 0/1/64/135 and exact accepted 136/137 secret vectors |
| `_absorb`, `_consume`, `update`, `_short_bytes`, `digest128` | Existing split-point coverage plus independent 240/241/1024/1025 checkpoints; varied 1/63/64/65/255/256/257-byte updates and empty updates; reset |
| `_hex64` | Existing canonical known answers plus binary 00/7f/80/ff canonical digest |

No missing boolean outcome is claimed solely from this source-to-stimulus map.
The next test additions must follow actual zero-hit rows or a newly identified
specification gap; duplicating boundary vectors cannot demonstrate 99%.

Measurement remains blocked on an admitted, source-matched pure-Simple
producer/runner and complete inventory+counts association. The current native
runtime collector creates rows when probes run; it must be joined with the
compiler's complete zero-count AST inventory (or equivalent LLVM mapping) so
uncalled functions remain in the denominator. First qualify the existing gate
selftest with its never-called function, then retain raw reports before cleanup.
Its metric is 100% both-outcomes-covered decision sites and condition sites,
not a 99% branch-outcome ratio. Report these metrics separately. Windows path
normalization and same-line decision identities also need actual admission.

Focused XXH3 overrides after admission:

```sh
HASH_COV_SCOPE='src/lib/common/crypto/xxh3.spl src/lib/common/hash/xxh3.spl'
HASH_COV_SPECS='test/01_unit/lib/common/crypto/xxh3_kat_spec.spl test/01_unit/lib/common/crypto/xxh3_reference_vectors_spec.spl test/01_unit/lib/common/hash/xxh3_spec.spl test/01_unit/lib/common/crypto/xxh3_128_spec_boundaries_spec.spl test/02_integration/lib/common/hash/xxh3_128_stream_contract_spec.spl test/03_system/lib/hash/xxh3_128_published_contract_spec.spl'
export HASH_COV_SCOPE HASH_COV_SPECS
SIMPLE_COV_BIN=<admitted-runtime> sh scripts/check/check-hash-algos-coverage.shs --report
```

Static shell syntax and default-path inclusion are the only checks applicable
without that runtime. They are not test execution or branch-coverage evidence.
All previously authored SSpec/manual statuses remain AUTHORED_UNRUN.
