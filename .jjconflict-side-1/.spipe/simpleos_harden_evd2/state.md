# EVD2 — evidence_receipt first consumers

## Goal
Make the fail-closed evidence receipt module (`std.spec.evidence_receipt`, §21.4)
real by wiring its first two consumers, closing the "zero consumers" gap behind
the ledger row "evidence: fail-closed on missing/stale artifacts not yet universal".

## Decisions
- Added two pure helpers to the module (kept IO-free, `receipt_to_sdn` still
  concatenation): `receipt_new(test_id, target, machine_or_qemu, result, artifacts)`
  one-line builder with explicit placeholder bookkeeping fields, and
  `verify_verdict(outcome) -> "PASS"|"FAIL"` so gates compare a machine string
  instead of re-deriving pass/fail. Both exported.
- Consumer 1 (arch guard): `test/01_unit/os/arch/duplicate_owner_spec.spl` new
  describe "Ledger parity emits a fail-closed evidence receipt" — receipt for
  `doc/08_tracking/os/production_status.sdn` (file_exists + file_modified_time via
  app.io.mod feed the pure rules) asserts verdict PASS; deliberate-red style
  example: receipt for a nonexistent path must yield FAIL on rule
  `artifact_present`.
- Consumer 2 (P6 gate): new `test/01_unit/os/toolchain/lld_gate_receipt_spec.spl`
  encodes the CURRENT truth of the authored-but-blocked lld gate: script
  `scripts/os/ssh_lld_link_uefi.shs` receipt = PASS; missing
  `build/os/clang_static/bin/lld_static` receipt = FAIL (asserted — FAIL is the
  honest state; the example goes red the day lld_static lands, forcing an
  upgrade to a real run receipt). Third example serializes the blocked receipt
  (machine_or_qemu: blocked, result: BLOCKED) via receipt_to_sdn.
- Ledger `evidence:` row note appended: "first two consumers wired (...)" — no
  other row touched.

## Evidence (build/evd2_job = copy of bin/release/x86_64-unknown-linux-gnu/simple)
- duplicate_owner_spec: 4 + 1 + 2 examples, 0 failures in every block (original
  Stage-S 4-example guard stayed green; +2 new receipt examples).
- lld_gate_receipt_spec: 3 examples, 0 failures.
- evidence_receipt_spec (module's own spec, post-API-add): 6 blocks, all
  0 failures.
- Known cosmetic: gc-warning "higher-layer module std.nogc_sync_mut.spec in
  nogc_async_mut context" on the toolchain spec — pre-existing family-warning
  class, not a failure.

## Next
- Wire receipt emission into an actual gate runner (spipe sdn receipts owner)
  so receipts are WRITTEN per release-gate run, not only asserted in specs.
- Freshness is exercised with run_start=0 in consumers (existence-gate);
  a real gate run should pass its true run_start for the stale-artifact rule.
- When lld_static lands, lld_gate_receipt_spec example 2 goes red by design —
  replace with a real run receipt and flip the ledger P6 row.
