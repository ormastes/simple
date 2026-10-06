# BLAKE2b block-boundary fixture oracles disagree with an independent provider

Phase1 row 23664 executed six legacy BLAKE2b cases: four passed, and exactly
the 128/129-byte repeated-ASCII-a cases failed. Both test/unit and canonical
test/01_unit copies contained the same incorrect expected constants. Local
tracking search found only a general test-tree inventory mention, not a
BLAKE2b oracle diagnosis; the existing fabricated BLAKE2s bug is a different
algorithm/criterion and remains separate.

For each size, the shell created a retained binary input containing exactly
128 or 129 copies of 0x61 using awk. Installed `/usr/bin/openssl` 3.0.13 ran
`openssl dgst -blake2b512 INPUT` once per input and exited 0. The retained
outputs independently match both actual SPL failure digests byte-for-byte:

- 128 bytes: `fc6c71f688f43ea7d60817478808f3cac753e61571865c95adbc2d9122c943a76b92c2cb1047ef3fe7bf6e436ec1d0a99a9e5b216780bf7fed9d7ca91d3a8f3b`.
- 129 bytes: `55e6e0eb418149a8af92fd9ddc99254781b2f522a131b4f4d984404b71a00e1167b8124d5dcddd4c6977b299392335d6edd303da6d344d74bbef2d38101b232b`.

Oracle input/output files: `/tmp/simple-blake2b-boundary-oracle-20261007`.
Input SHA256: 128 bytes `6836cf13bac400e9105071cd6af47084dfacad4e5e302c94bfed24e013afb73e`;
129 bytes `c12cb024a2e5551cca0e08fce8f1c5e314555cc3fef6329ee994a3db752166ae`.
Provider SHA256 `b4f547c0f16272d1cc7f870330a6f2c243710c335e7a99c734ff7a0c6fdb2503`.
Owner SHA256 `4c3956b39e3772bc3f0fa39bfcab95cc0d3189845e0d815a1a19c7acfbd53de7`.
The private `evidence/inputs.sha256` binds retained inputs, outputs, provider
and frozen owner. No crypto implementation defect is established by these
failures, and neither expected value is taken solely from the implementation.

Original result `/tmp/simple-phase1-per-row-attempt-20261006/23664/result.json`
SHA256 `f95b6128fb48890ff4c4870e86afe36e748274c742ce2d664a7ee7521073ae5d`;
original output is retained under frozen source build/test-artifacts/unit/os/crypto/blake2b.
The narrow repair changes only two expected digests and their attribution
comments in each copy, preserving all six cases and all other assertions.
The one-shot owner exposes no streaming API; none is invented for this fix.
Each changed copy passed its separate pinned Phase1 diagnostic run. Seed
lineage does not imply self-hosted/native crypto or whole-bootstrap admission.
No unchanged green cases are replayed as an independent qualification gate.
Provider tokens/cache/cohort metrics are unavailable and are not guessed.

## Actual changed-copy verification

Release base: `7166088252471630d1a4da8ebadd1b8ba1bedff8`.
Both changed files preserve their six original scenarios and real assertions.
Legacy source SHA256 `72e00373f5f1ee2d6ff53b6f7dbe322298203b38b41d1050179b73901f88a701`;
canonical SHA256 `4745015ed2516cb67cfc77abc699b9a72409b4ed2476a024094ce0002beed3f6`.
The only copy difference remains preexisting formatting.

- Legacy actual 6/6, zero failures/skips, 432ms file duration (435ms root aggregate). Artifact: `/tmp/simple-blake2b-boundary-fixture-fix-20261007/build/test-artifacts/unit/os/crypto/blake2b/result.json`; observation `/tmp/simple-blake2b-legacy-fixture-result-20261007`; kernel `/tmp/simple-blake2b-legacy-fixture-kernel-20261007`, exit 0/quiescent 1.
- Canonical actual 6/6, zero failures/skips, 386ms file duration (389ms root aggregate). Artifact: `/tmp/simple-blake2b-boundary-fixture-fix-20261007/build/test-artifacts/01_unit/os/crypto/blake2b/result.json`; observation `/tmp/simple-blake2b-canonical-fixture-result-20261007`; kernel `/tmp/simple-blake2b-canonical-fixture-kernel-20261007`, exit 0/quiescent 1.

Seed SHA256 `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`;
frozen source `e59027c353e9ed6ea8ddf572424da70e188fe511`.
Neither passing copy was replayed. Sidecar review is N/A for this narrow
independently established oracle correction.

## Manuals and scoped review

Each copy's canonical SPL docgen ran once and completed one manual with zero
stubs. All six executable scenario statement bodies match its tested source;
generated bodies are retained beneath reviewed factual provenance headers.
Receipts: `/tmp/simple-blake2b-{legacy,canonical}-docgen-20261007` and their
corresponding private kernel directories, exit 0/quiescent 1 each.
Each copy's single scoped scan reports CURRENT, score 92, release_ready true,
blockers 0; dimensions narrative/structure/oracle/traceability 100, evidence
55, coverage 100, maintainability 90. Receipts:
`/tmp/simple-blake2b-{legacy,canonical}-scan-20261007`, kernel exit 0/quiescent 1.
Reviewed nonblocking findings concern existing folded step/capture metadata
and heading-based recovery recognition. The human-reviewed headers state
exact inputs/oracle identity and recovery limits; no assertion is weakened.
Working/staged environment guards, zero executable specs in doc/06_spec and
exact staged diff checks pass for the five-file test-only change. No passing
test, docgen or scan was replayed. This is scoped verification and does not
change whole-bootstrap/native crypto qualification.
