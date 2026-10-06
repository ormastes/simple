# BLAKE2s 65-byte fixture had an incorrect known answer

Phase1 row 22519 executed nine examples in
`test/unit/lib/crypto/blake2s_spec.spl`: eight passed and only the 65-byte
repeated-`a` known-answer assertion failed. It expected `b4ee6c...`.
An independently executed installed OpenSSL BLAKE2S-256 provider returned
`045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497`
for exactly 65 ASCII `a` bytes. The test constant was wrong; no production
crypto defect has been established.

The correction preserves the assertion and replaces its oracle. A new 64+1
streaming partition checks the same message against the independent known
answer, exercising the block/residual API boundary. The eight previously
passing cases and production implementation remain unchanged.

## Actual evidence and scope

- Original result: `/tmp/simple-phase1-per-row-attempt-20261006/22519/result.json`, 8/9, zero skipped, 149ms. Its computed digest was not retained.
- Oracle: `/tmp/simple-blake2s-65-byte-fixture-fix-20261006/evidence/observed-openssl-oracle.txt`, explicitly a transcript of the actual tool output, not a fabricated canonical admission receipt. The digest command executed once and exited 0; it was not repeated to manufacture a capture.
- OpenSSL 3.0.13 identity, exact 65-byte input and implementation bytes are bound in `evidence/oracle-inputs.sha256` beside that receipt.
- Changed original file plus partition regression: 10/10, zero failures/skips, 208ms file duration (210ms aggregate report). Artifact: `/tmp/simple-blake2s-65-byte-fixture-fix-20261006/build/test-artifacts/unit/lib/crypto/blake2s/result.json`.
- Kernel: `/tmp/simple-blake2s-65-byte-fixture-fix-kernel-20261006/kernel-containment-terminal.env`, exit 0, quiescent 1.
- Exact tested spec SHA256: `ebd2e517ae18c29ee66d9f5d4bba276a74bc78c45c5751644cf6fdc0380c54ea`.
- Compiler SHA256: `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`; frozen dependency source: `e59027c353e9ed6ea8ddf572424da70e188fe511`.

This is authorized Phase1 diagnostic seed evidence for a test-fixture repair,
not self-hosted compiler, native crypto, constant-time, or whole-bootstrap
qualification. No already-green tests are replayed. Manual generation and
quality review are separate checks; no new feature requirement is fabricated.
The legacy source's claim that interpreter mode never executes digest
assertions is not used as evidence: this actual failed-then-passed criterion
retains positive example counts and kernel receipts. Sidecar review is N/A for
this narrow oracle correction and partition regression.

Provider input/output/cache-read/cache-create tokens: unavailable. Comparable
cohort average and ratio: unavailable; no usage values were guessed.

## Manual and scoped verification

Canonical SPL docgen completed once: one complete manual, zero stubs, kernel
exit 0/quiescent 1. Receipts: `/tmp/simple-blake2s-65-byte-docgen-20261006` and
`/tmp/simple-blake2s-65-byte-docgen-kernel-20261006`. A reviewed factual header
records the exact source hash and oracle/execution provenance; the generated
body is preserved. All ten scenario statement bodies match current source
under canonical indentation normalization (SHA256 `673610fd320b333f5727281626e62741677af104345234bf9b5cef14aed3b524`).

The single SSpec scan exited 0, kernel quiescent 1, manual CURRENT, aggregate
88, release_ready true, blockers 0. Dimensions: narrative 100, structure 90,
oracle 100, traceability 100, evidence 55, coverage 100, maintainability 70.
Receipts: `/tmp/simple-blake2s-65-byte-sspec-scan-20261006`. Reviewed nonblocking
warnings concern existing folded-unit step/capture metadata, the original
65-byte case's absent step label, and heading-based guidance/limitations
recognition. Human-reviewed scope/recovery prose and the actual assertion
receipts remain explicit. The legacy `@manual scenario evidence` visibility
warning predates this change; it is not a dummy pass or altered test oracle.
No scan or passing test was replayed. This is scoped test-only verification,
not full compiler/library release qualification.
