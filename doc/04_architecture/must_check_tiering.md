# Mandatory Check Tiering Architecture

The registry (`config/check/must_check_gates.sdn`) is policy. The bootstrap
runner is the sole evidence producer. The textual ledger
(`doc/08_tracking/check/must_check_db.sdn`) is retained state. The push runner is
a read-only consumer of the ledger and committed Git trees.

Trust flows in one direction:

`bootstrap phase artifacts -> per-phase verifiers -> automated gates + retained logs -> atomic SDN ledger -> push`

The push consumer recomputes a content fingerprint excluding the ledger itself,
requires one-to-one unique registry/result IDs and exact command agreement,
retains a per-gate PASS time, and verifies each PASS evidence file against its
recorded SHA-256. It fails closed on malformed, stale, failed, missing,
tampered, evidence-less, or non-passing push-blocking rows. Non-blocking TODOs
remain visible. Push-tier commands are registry rows dispatched through a
closed ID/mode/command allowlist, so a changed manifest cannot turn the hook
into an arbitrary shell-command executor.
The bootstrap owner writes logs before the ledger and records repository-relative
evidence references and hashes. This avoids a circular Git hash dependency
while binding PASS evidence to the source/config/scripts/tests/docs it qualifies.
Ledger schema v3 also binds every result to a non-empty owner. A non-passing
row must retain an actionable unblock condition; a passing row must use
`unblock_condition=none`. The push consumer rejects unowned work, vacuous TODOs,
and PASS rows that still claim unresolved work.
