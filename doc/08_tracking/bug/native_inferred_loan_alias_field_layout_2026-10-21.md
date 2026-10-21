# Native inferred `LoanAlias` field layout mismatch — 2026-10-21

## Symptom

The MIR-adapter native probe build succeeded, but its first qualified runtime
probe segfaulted in `compiler.borrow.borrow_check.ownership_flow.ownership_write_covers`
(exit 139 under the 30-second guard, after about 0.98 seconds). The debugger
stack repeatedly recursed through that function. See
`build/nogc-hardening/mir_adapter-feature-run-2.log`,
`build/nogc-hardening/mir_adapter-feature-gdb-2.log`, and
`build/nogc-hardening/mir_adapter-feature-registers-2.log`.

## Evidence and source

The relevant source is `src/compiler/55.borrow/borrow_check/ownership_flow.spl`,
`ownership_write_covers`, which reads the projected place carried by a
`LoanAlias`. The declared field access is centralized in
`src/compiler/55.borrow/borrow_check/nll.spl`, `loan_alias_place` (currently
around line 317), which returns `alias.place`.

In the r17 native binary, the crashing `ownership_write_covers` disassembly at
text offset `0x19b08` reads the alias base at offset `+0` (`loan_id`) where it
needs the `Place` field. The `LoanAlias` constructor places `Place` at offset
`+8`. Thus the inferred native field access uses the wrong layout for this
alias in this generic-loop path. The debugger disassembly/register capture is
preserved in the logs above.

## Workaround and status

Use the declared, typed accessor `loan_alias_place(alias)` at the read site so
the native backend receives the `Place` field through an explicitly typed
function boundary. This is a source-level workaround for an r17 inferred alias
field-layout defect; it does not fix or establish a compiler/backend repair.
The producer binary was not rebuilt for this workaround. Producer used for the
probe: `/home/yoon/dev/simple-lane-boot7/.simple/storage/build/bootstrap-r17/stage2/aarch64-unknown-linux-gnu/simple` (SHA-256 `29dd8539f3fe8e01df9b227e0621b20953fd736e239dafef8bafae8918abb3c2`).

A final adapter qualification cycle is pending. The third native call-loan and
adapter builds are also pending at the time of this report. No acceptance
criterion is signed off by this bug report.
