# OS BLAKE3 exact key contract repair — 2026-11-03

Status: SOURCE_REVIEW_PENDING / AUTHORED_UNRUN / BRANCH_UNMEASURED. No admitted source-matched runner is available; no bootstrap or seed fallback was attempted. No runtime RED/GREEN receipt exists, so this is not an executed defect closure.

Owner: `src/os/crypto/blake3.spl`, distinct from `src/lib/common/crypto/blake3.spl` (whose branch evidence cannot be credited here).

## Concrete source discrepancy

The public OS `blake3_keyed` docstring requires exactly 32 key bytes. It previously called `_b3_key_words(key)` without validation. That helper iterates eight times and `_b3_le32_load` unconditionally indexes offsets `4*i` through `4*i+3`. Thus the only key bytes read are indices 0..31, independently of key length. A 33-byte key ignores its last byte and reaches normal hashing; a 0/31-byte key attempts reads outside the provided buffer. This is a direct control/dataflow proof, not a host runtime observation. It demonstrates violation of the exact-key contract without assuming a particular runtime's bounds failure mode.

The common implementation already returns [] when key.len() !=32. The repair adopts that fail-closed result in the OS public API, before any word read. No compression, key derivation, tree merge or valid-key path changes. PDF section 2.3 defines keyed hashing using a 256-bit key; the empty-result error representation is the repository's API policy, not prescribed by the PDF.

## Regression and specification mapping

New executable: `test/01_unit/os/crypto/blake3_key_contract_spec.spl`.
Authored mirror: `doc/06_spec/01_unit/os/crypto/blake3_key_contract_spec.md`.

| Canonical requirement | Added OS scenarios | Purpose |
|---|---|---|
| REQ-HASH-BLAKE3-001 | Official hash lengths64,65,1023,1025 | Full/partial compression block and chunk transition |
| REQ-HASH-BLAKE3-002 | Official hash2049,3073 | One stack entry after completed-subtree merge; multiple stack entries/right fold |
| REQ-HASH-BLAKE3-003 | Key lengths0,31,33 rejected; official keyed1025 and derive3073 | Repaired guard both sides plus mode flags across trees |
| REQ-HASH-BLAKE3-004 | Official hash3073, output65 bytes | Root output counter increments and last partial output word |

Existing `blake3_kat_spec.spl` covers empty hash/keyed/derive and hash1/63/1024; these are not duplicated. The new source calls only the OS owner, compares literal published expected bytes, and does not use common-owner output as oracle. No new fixture or foreign implementation is introduced.

Source identity: BLAKE3-specs PDF commit ac784c9f22a48327782f042ec2f4d8126b3b1744, SHA256 ce179e62f29a6e43ec1ac2fe62b5e063a18632cf936c430d1373bfa0b81fb349. Published vectors BLAKE3 commit f55849f89cd85083c1c9daa2c5de20766f309c00, SHA256 dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624. Input repeats0..250; key/context copied exactly. The manual includes canonical spec/vector hashes and explicitly has no run artifact.

Required remaining validation: source review by Astra; admitted native runner executes old/new guard regression and positive vectors; actual docgen reports zero stubs; measured per-owner branch inventory includes zero-hit sites. No99% claim or exclusion is justified. No streaming API exists. Broader missing OS mode/binary ff cases remain outside this bounded guard repair. Source-only review is not test execution. Merge owner /root/land_source_repairs; final reviewer /root/astra_phase3_review; sidecars N/A.
