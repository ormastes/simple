# A fabricated BLAKE2s KAT would have condemned a correct implementation
## Closed 2026-09-16 — Status FIXED; wrong KAT vector corrected in both spec copies

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** FIXED (vector corrected in both spec copies; filed for the pattern)
**Found:** 2026-08-04
**Severity:** high — the wrong value was attributed to a named reference tool
(`hashlib.blake2s`), so the natural response to the red test is to "fix" the
hash implementation until it reproduces a digest no BLAKE2s ever produces

## Symptom

`test/01_unit/lib/crypto/blake2s_spec.spl` (and its legacy duplicate
`test/unit/lib/crypto/blake2s_spec.spl`) asserted:

```
it "65-byte input (one full block + 1 residual byte) 32-byte digest":
    # Python: hashlib.blake2s(b'a'*65).hexdigest()
    #   b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db
```

Against a fresh RFC 7693 implementation the run reported:

```
Results: 9 total, 8 passed, 1 failed
expected 045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497
      to equal b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db
```

Expected (per the comment): `b4ee6ca1…`. Actual: `045f8ae1…`.

## Root cause

The recorded vector is not the BLAKE2s-256 digest of 65 `a` bytes. Independent
confirmation from OpenSSL, which shares no code with this tree:

```sh
$ printf 'a%.0s' $(seq 1 64) > /tmp/a64.bin
$ printf 'a%.0s' $(seq 1 65) > /tmp/a65.bin
$ openssl dgst -blake2s256 /tmp/a64.bin /tmp/a65.bin
BLAKE2S-256(/tmp/a64.bin)= 651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
BLAKE2S-256(/tmp/a65.bin)= 045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497
```

OpenSSL agrees with this tree's implementation on BOTH inputs, including the
64-byte one the same spec file already asserted and passed. Three further
authoritative vectors in the same file also pass unmodified: the RFC 7693 empty
digest (`69217a30…`), the RFC 7693 Appendix B `abc` digest (`508c5e8c…`), and
two keyed vectors from `blake2-kat.json`. The 65-byte entry is the only one in
the file that no reference implementation reproduces.

The 65-byte case is the file's only *multi-block unkeyed* vector, so it is
precisely the vector that pins the update-boundary compression. A wrong oracle
there is maximally expensive: it points the reader at the one code path the
other vectors do not cover.

`src/lib/common/crypto/blake2s.spl:150` (`blake2s_update`) is correct as
written — a full buffer is compressed only when the *next* byte arrives, never
on the 64-byte boundary itself, so the RFC's final-block flag lands on the last
block.

## Fix applied

Both spec copies now assert `045f8ae1…`, and the comment cites the reproducible
`openssl dgst -blake2s256` command instead of an unverifiable claim about what
some Python session printed.

## Why this is filed rather than closed silently

This is the fourth fabricated crypto test vector found in this tree (see
`fabricated_crypto_test_vector_in_bip39_kat`, the ed25519 KAT note, and the
ZUC-128 keystream entry). The shared shape: a hand-written digest attributed to
a named tool in a comment, with no command recorded that anyone could re-run.
A KAT whose provenance cannot be re-executed is not a known-answer test.
Vectors should either come from the standard's own appendix or carry the exact
command that regenerates them.


## 2026-10-06 follow-up: current release copies again contain the fabricated oracle

At release base `e96ac7b22a5cacf15f2467185dd335ed1221c5f7`, both
`test/01_unit/lib/crypto/blake2s_spec.spl` and the legacy
`test/unit/lib/crypto/blake2s_spec.spl` contain the wrong `b4ee6c...`
constant. The earlier FIXED history above is preserved; it does not describe
these current bytes. The existing generated legacy manual already contained
the correct `045f8a...` answer, exposing source/manual drift. This follow-up
repairs both fixture copies, each independently executed once. The canonical `test/01_unit`
copy passed its changed-source diagnostic criterion; the legacy PASS was preserved without replay.


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

### Actual evidence and scope

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

### Manual and scoped verification

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

### Canonical-copy changed-source evidence

The canonical `test/01_unit/lib/crypto/blake2s_spec.spl` retains its original
formatting and eight other cases, applies the independently established oracle,
and adds the same 64+1 partition. Exact tested SHA256:
`4d4518d24ff6e403a7011cee629614d437a46a1b2794db5e477acb6227d5d2ea`.
It executed 10/10, zero failures/skips, 373ms file duration (377ms aggregate),
using the same pinned Phase1 diagnostic seed and frozen dependency source.
Result: `/tmp/simple-blake2s-canonical-fixture-fix-20261006/build/test-artifacts/01_unit/lib/crypto/blake2s/result.json`.
Root observation: `/tmp/simple-blake2s-canonical-fixture-fix-result-20261006`.
Kernel: `/tmp/simple-blake2s-canonical-fixture-fix-kernel-20261006`, exit 0,
quiescent 1. Neither passing fixture was replayed.

Canonical-only docgen completed once with one complete manual and zero stubs;
all ten executable scenario statements match current source. Receipt:
`/tmp/simple-blake2s-canonical-docgen-20261006`, kernel exit 0/quiescent 1.
Its single scoped SSpec scan reports CURRENT, score 88, release_ready true,
blockers 0, with the same seven dimension scores and reviewed nonblocking
metadata/heading warnings described for the legacy copy above. Receipt:
`/tmp/simple-blake2s-canonical-sspec-scan-20261006`, kernel exit 0/quiescent 1.
Both generated bodies are preserved beneath truthful source/evidence headers.
Changed-scope environment guards, zero executable specs under doc/06_spec,
and exact staged diff checks pass; unrelated live collector inputs are intact.
