# RTL source audit admission and wiring

This repairs one concrete owner in
`guard_wiring_optout_false_exemptions_2026-08-06`; the broad bug remains open.
The RTL audit's exemption explicitly said that its hardware claim was false
and wiring was pending. A source-only CI job now executes the audit, and that
single exemption is removed. This is a structural source audit, not hardware
execution or instruction-set qualification.

The audit previously returned success when no VHDL input existed. It now exits
2 with a false verdict and zero checked files. Explicit `--lane` arguments also
fail with exit 2 if missing or empty, including mixed valid/unavailable inputs.
Default optional lane directories may remain absent when other source is
actually checked. Nonempty audits report their checked-file count.

The executable contract in
`test/01_unit/scripts/riscv_rtl_truth_contract_test.shs` copies the production
checker into a small real Git source tree. It checks the former zero-input
success, missing and empty explicit lanes, mixed available/unavailable lanes,
a valid handwritten RTL source, and the existing scripted-core and undefined
entity negative fixtures. The workflow runs this contract before auditing the
actual repository source, with no success override or advisory failure flag.

No other exemption, gate, or frozen unwired baseline is changed. Validation
receipts and exact counts are retained with the PR; this change does not claim
the remaining false exemptions or their underlying failures are repaired.
