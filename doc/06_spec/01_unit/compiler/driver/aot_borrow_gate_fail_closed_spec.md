# AOT mandatory borrow gate

**Evidence status:** authored operator manual; generated docgen and execution verification pending an admitted full pure-Simple runtime. No PASS claimed.

Source: `test/01_unit/compiler/driver/aot_borrow_gate_fail_closed_spec.spl`.

1. Construct real MIR with Move followed by Copy of its moved source.
2. Enable durable strict policy and the explicit bypass, then call stage_emit_object with bootstrap settings.
3. Require BorrowError containing NOGC-POLICY-002 after HIR eviction, for both clean and conflicting MIR.
4. Without the bypass, accept clean MIR and reject the moved source.
5. Preserve legacy explicit bypass and earlier-error attribution.

Requirements: no-GC recovery §3.7 and AC-CYCLE-04/AC-GATE-02. This focused gate does not complete either broad acceptance row.
