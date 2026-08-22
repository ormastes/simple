# Must-Check Tiering Requirements

The user selected a two-tier mandatory-check contract: interactive push checks
stay bounded, while bootstrap owns expensive evidence and persists results in a
textual SDN ledger.

## Requirements

- REQ-MCT-001: `check-push-must-pass.shs` must execute only bounded committed-
  tree checks and ledger validation. It must not launch compiler bootstrap,
  native builds, whole tests, QEMU, hardware, or performance campaigns.
- REQ-MCT-002: `check-bootstrap-must-pass.shs` must own expensive automated
  gates and compiler Stage 1-4 receipt admission, accepting only an explicit
  final PASS verdict and writing its ledger atomically.
- REQ-MCT-003: The textual ledger must bind a stable gate ID, source
  fingerprint, status, command, time, evidence path/hash, owner, and unblock
  condition. Stale, malformed, unowned, vacuous, or tampered state fails closed.
  A TODO receipt may earn its first PASS only through an explicit producer
  command and a committed `simple.must-check-gate-receipt/v1` bound to the gate,
  fingerprint, final PASS verdict, and a separate committed artifact hash; that
  PASS remains durable while the same committed blob and hash remain present.
- REQ-MCT-004: A successful bootstrap-produced ledger must be consumable by the
  next committed-ref push check without rerunning expensive work. Before the
  first successful promotion, the canonical all-TODO `unrecorded` ledger must
  remain visible but must not suppress bounded structural push gates or force a
  whole-hook bypass. Promotion is monotonic: a ref descending from real PASS
  evidence may never reset to the unrecorded baseline.
- REQ-MCT-005: Unfinished sdoctest, Caret, server/GPU, SimpleOS/SBC/QEMU,
  RISC-V/VHDL, size, startup, and benchmark outcomes remain visible bootstrap
  TODO/blocked rows and never count as PASS. Deleting a required ID from both
  registry and ledger must fail; two mutable files cannot collude to erase debt.
- REQ-MCT-006: Unix and Windows setup scripts must install the dispatcher while
  preserving unrelated local hooks. An exact legacy canonical copy or symlink
  may be replaced without destroying its already-preserved payload.

## Exclusion

This requirement set hardens scheduling and evidence ownership. It does not
claim the broader hardware and performance TODOs have been implemented.
