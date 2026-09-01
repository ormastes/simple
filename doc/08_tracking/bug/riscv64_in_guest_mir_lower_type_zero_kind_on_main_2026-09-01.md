# riscv64 in-guest: MIR lowering rejects `main` with a raw-0 HirType kind

- Status: **OPEN** — the current blocker for goal item 1 row 2, and a NEW one.
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
  row 2 (`buildrun`)
- Measured under real OpenSBI v1.4 `-bios fw_payload` (never `-kernel`, never
  `isa-debug-exit`), nonce `41d7bd8ce8c848bd`, gate selftest OK (23 fixtures).

## Symptom, measured

```
[buildrun] phase=hir-ok
[buildrun] FAIL mir lowering error: E-MIR-TYPE-ZeroKind: lower_type received a
  well-formed HirType whose `kind` field is raw 0 (never written) while
  lowering 'main' -- fix the PRODUCER that left kind unset, not lower_type
```

## Why this is genuinely NEW, not the old blocker resurfacing

The previous blocker
(`riscv64_freestanding_toplevel_decl_walk_names_both_functions_add_2026-09-01.md`)
was that `main` never existed at all: the top-level walk converted declaration 0
twice, so `parsed.functions` held only `add`, `lookup_or_invalid("main")`
answered `-1`, and the run stage reported "module has no main function". That is
fixed and verified. `main` now exists, lowers to HIR, and is being lowered to
MIR — the error message names it. This is the **first time `main` has been
observed downstream on this row.**

## Lead, NOT yet measured

The program's `main` is declared `fn main():` — no return type. The suspicion is
that the producer of the implicit unit/void return `HirType` leaves `kind` at
its zero value on the freestanding path, and that `add` is unaffected because it
declares `-> i64` explicitly. **This is a hypothesis and must be measured before
being acted on**; the previous blocker on this row cost three sessions precisely
because four successive plausible hypotheses were assumed rather than probed.
The productive technique there, after external probes kept refuting each theory,
was instrumenting the suspect function's own branch decisions into an in-memory
trace and printing it from the entry — the same approach applies here to
whichever producer builds that HirType.

The diagnostic itself is well-behaved and fails closed with an accurate message
naming the function; it is not the defect.
