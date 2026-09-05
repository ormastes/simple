# Local Research: Must-Check Tiering

The installed pre-push owner is
`scripts/check/pre-push-conflict-tree-guard.shs`. Before this lane it invoked
dozens of full-tree and compiler probes, including native builds documented as
taking minutes, making a ten-second push target impossible by construction.

The bootstrap already owns authoritative phase evidence:

- Stage 2/3: `check-bootstrap-stage3-selfverify.shs --full-provenance` validates
  the admitted manifest, hashes, authority, and both sanity receipts.
- Stage 4: `check-post-bootstrap-stage4-sspec.shs` binds the exact executable,
  provenance, source, and essential-tool smoke evidence.

The appropriate split is therefore committed-tree checks at push time and
receipt validation/expensive execution at bootstrap time. A tracked textual SDN
ledger makes unfinished mandatory goals visible without executing them in the
interactive hook.
