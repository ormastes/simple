# Stage 3 resume replays admitted Stage 2 checks

- **Status:** Structural receipt-reuse fix implemented; verification pending.
- **Owner:** Bootstrap Stage 3 provenance and admission receipts.

## Failure

`--stop-after-stage2` executes the Stage 2 sanity and struct-receiver gates and
retains their PASS evidence.  `resume-stage3-from-admitted.sh` then calls the
live sanity verifier again, and successful Stage 3 manifest writing and
verification replay the same Stage 2 executable yet again.

This violates the bootstrap session rule that a green criterion is executed at
most once.  It also confuses receipt verification with test execution: the
admitted Stage 2 artifact, source identity, runtime, tool authority, command,
and evidence hashes are already frozen.

## Required behavior

- Stage 2 sanity and receiver gates execute once while admitting that exact
  Stage 2 identity.
- Stage 3 resume and provenance verification structurally validate and reuse
  those receipts without executing the Stage 2 compiler.
- The Stage 3 provenance manifest binds both Stage 2 receipts and records an
  identity-scoped receipt-reuse policy with zero Stage 2 replays.
- Stage 2 admission atomically publishes a mode-0400 `admission.env` inside
  the private mode-0500 admitted-artifact directory.  That receipt binds the
  candidate, source, runtime, tool, build-argument, sanity, and receiver hashes;
  resume and manifest admission must match it rather than recomputing authority
  from mutable evidence alone.
- Any artifact, source, runtime, tool, command, receipt, or receiver-log hash
  mismatch fails closed.
- Stage 3 candidate sanity remains a distinct live admission criterion.

The criterion identity is scoped by the Stage 2 artifact, source snapshot,
runtime snapshot, tool authority, build arguments, sanity receipt, and receiver
receipt.  A fixed-source Stage 2 candidate has a new identity, so its admission
checks are new criteria rather than reruns of the prior Stage 2 checks.

## Planned focused coverage

- Structural sanity receipt verification succeeds without invoking the
  candidate or frontend smoke helper and requires both frontend modes to pass.
- Structural receiver receipt verification binds candidate, runtime snapshot,
  probe log, and all PASS fields and rejects tampering.
- Admission verification rejects candidate, admission-receipt, and receiver-log
  tampering; schema v3 Stage 3 provenance fails closed.
- Stage 3 provenance schema v4 requires the receipt-reuse policy, receiver
  evidence, identity hash, one admission execution, and zero Stage 3 replays.
