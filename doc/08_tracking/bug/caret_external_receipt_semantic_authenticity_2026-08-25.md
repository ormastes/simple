# Caret external receipt semantic authenticity gap

Status: fixed 2026-11-11 (lane ne3) — fail-closed quarantine restored and
re-verified live (regression test PASS: all five generic signed Caret receipts
fail closed at the semantic quarantine). The five rows remain `TODO` pending
the versioned validators below; that is deliberate tracked follow-up, not an
open defect. See "Addendum 2026-11-11" at the end of this file.

`check-external-must-check-receipt.shs` previously accepted a trusted signature
over four generic blobs and exact `acceptance.*=PASS` labels for local Slang,
installed providers, runtime primitives, production multi-manager, and smux.
That proves reviewer identity and blob integrity, not provider generation,
process reaping, concurrent supervision, or real PTY ownership. Provisioning a
trusted key would therefore have enabled semantic fabrication. The importer now
fails these gates closed after signature authentication and before generic
attachments can promote a row.

## Status 2026-11-05 — quarantine restored, regression fix verified

The fail-closed quarantine for the five external Caret rows was lost when the
main tree was transplanted onto release/1.0 (88aac2ffe28 removed both the
quarantine and its test harness from the pre-transplant state at d55b54e548e),
reopening the exact fabrication path this bug documents: a trusted signature
plus well-formed generic `acceptance.*=PASS` labels reached evidence-attachment
loading and would have promoted a row.

Fix: restored the post-authentication, pre-attachment quarantine in
`scripts/check/check-external-must-check-receipt.shs` (immediately after the
reviewer-signature `openssl dgst` verification, before any evidence blob is
loaded). All five rows
(`caret-local-llm-launch`, `caret-installed-provider-launches`,
`caret-agent-runtime-primitives`, `caret-production-multi-manager-launch`,
`caret-smux-multi-launch`) now fail with
`caret-semantic-validator-not-implemented-<gate>`.

Coverage: new self-contained regression test
`test/01_unit/scripts/caret_external_receipt_semantic_quarantine_test.shs`
builds a fixture reviewer key + policy + committed evidence blobs, signs a
generic artifact per Caret row, points the first attachment at a hostile path
to prove quarantine ordering (after signature authentication, before
attachment loading), and asserts the quarantine failure for all five rows.
TDD evidence: RED — before the fix the validator admitted the signed receipt
past authentication (test observed `unsafe-evidence-path` only because the
attachment path was deliberately hostile); GREEN — after the fix all five rows
fail closed (`PASS: all five generic signed Caret receipts fail closed at the
semantic quarantine`).

The versioned lane-specific validators listed below remain the follow-up work
required to ever promote these rows; the quarantine stays until they land. The
wrapper, messaging, and batch-adapter rows remain separate bootstrap checks.

## Required versioned validators

All new contracts must retain clean-HEAD producer/checker snapshots, exact
source fingerprint, target/toolchain identity, monotonic events, and an unsigned
reviewer-ready manifest. Authenticate the signature before loading or executing
evidence attachments.

- Installed providers: executable path/hash/version, provider-distinct argv,
  nonce prompt/parsed response, deadline, PID-start identity, waited exit,
  process-group/descendant census, and redacted leak scan. Echo fixtures prove
  wrapper structure only.
- Runtime primitives: distinct cancel and stop plus
  launch→running→cancel/stop→waited-exit, PID anti-reuse, escalation,
  PGID ownership, descendants before/after, and zero survivors.
- Multi-manager: all provider children concurrently live across timestamped
  polls under one parent, followed by waited/reaped children and descendants.
- smux: one real session/pane/PTY per Caret child, nonce capture, observed
  resize, cancel/stop/wait/close, and zero PID/fd survivors. Display-only
  `AgentTmuxEmbed` and in-memory `smux/api.spl` rows are not PTY evidence.
- Local Slang: first implement a production generation endpoint and Caret
  provider. Loader/readiness and `local_torch` cannot substitute. Then retain
  artifact/provider identity, readiness, nonce generation, timeout, waited
  stop, descendants, and leak-free cleanup.

The automated wrapper, messaging, and batch-adapter rows remain separate
bootstrap checks and must never promote these production rows.



## Addendum 2026-11-11 — lane ne3: FIXED — fabrication path closed; quarantine
## re-verified live on this lane

Traversed on work/p3-ne3-20261111 (origin/release/1.0.0 tip 93490a99c5d8).

The 2026-11-05 regression fix was re-executed here, not just re-read:

```
$ sh test/01_unit/scripts/caret_external_receipt_semantic_quarantine_test.shs
PASS: all five generic signed Caret receipts fail closed at the semantic quarantine
(exit 0)
```

(log: `build/review/p3fix-ne3-20261111-logs/row7_quarantine_test.log`). The test
builds a fixture reviewer key + policy, signs a generic artifact per Caret row
(installed-provider, runtime-primitives, multi-manager, smux, and the local
row's gate list in `check-external-must-check-receipt.shs:157`), points the
first attachment at a hostile path to prove quarantine ordering, and asserts
the post-authentication/pre-attachment failure for all five rows — all five
fail closed as required.

Residual, deliberately out of scope of the defect itself: the five external
rows remain `TODO` until the versioned lane-specific validators listed above
land (installed providers, runtime primitives, multi-manager, smux PTY,
local-Slang generation endpoint). That follow-up is a feature effort, not an
open security hole: with the quarantine in place, a trusted signature over
generic blobs can no longer promote a row.
