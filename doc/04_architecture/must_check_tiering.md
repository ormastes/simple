# Mandatory Check Tiering Architecture

The registry (`config/check/must_check_gates.sdn`) is policy. The bootstrap
runner is the sole evidence producer. The textual ledger
(`doc/08_tracking/check/must_check_db.sdn`) is retained state. The push runner is
a read-only consumer of the ledger and committed Git trees.

Trust flows in one direction:

`bootstrap phase artifacts -> per-phase verifiers -> automated gates + retained logs -> atomic SDN ledger -> push`

The push consumer recomputes a content fingerprint excluding the ledger itself,
requires one-to-one unique registry/result IDs, retains a per-gate PASS time,
and fails closed on malformed, stale, failed, missing, evidence-less, or
non-passing push-blocking rows. Non-blocking TODOs remain visible. The bootstrap
owner writes logs before the ledger and records repository-relative evidence
references. This avoids a circular Git hash dependency while binding PASS
evidence to the source/config/scripts/tests/docs it qualifies.
