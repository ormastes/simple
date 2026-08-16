# Simple RISC-V Hardening AC-5 — System Test Plan

## Scope

`REQ-RISCV-HARDEN-005` requires removal of the unreachable RV32 scratch array,
all scratch-address guards, and the payload-specific return-address overrides
from the production structured VHDL generator and pinned golden.

Excluded: Phase-4 bootstrap work, FPGA/silicon qualification, QEMU boot,
unrelated RISC-V trap/profile criteria, and the RV64 datapath.

## Environment and admission

- Repository root with the lane changes applied.
- An admitted pure-Simple full CLI for runtime, docgen, and maintenance.
- Rust seed and fallback-stub artifacts are forbidden.
- Missing admission, signal exit, runtime error, or absent output produces
  `TEST_BLOCKED`/FAIL and never a substitute PASS.

## Execution order

1. Run static, layout, environment, numbered-artifact, conflict, and
   changed-file guards.
2. With an admitted full CLI, run the executable system spec once.
3. Regenerate only its mirrored Markdown manual and inspect visible steps.
4. Run `sspec-maintain scan` once and inspect all seven scores, blockers,
   mirror state, and requirement traceability.
5. Run the golden-match and focused RV32 GHDL gate when the qualified
   environment is available.

## Scenario matrix

| Scenario | Class | Required result |
| --- | --- | --- |
| Production generation | Positive | Real RV32/ROM markers present; dead-scratch oracle returns no error |
| Golden equivalence | Positive | Nonempty pinned golden equals complete generated VHDL |
| Debug aspect | Edge | Debug surface toggles while both products remain scratch-free |
| Stale calibration | Error | Empty and four historical stale classes return stable fail-closed errors |

## Traceability

| Requirement | Source | Executable spec | Manual | Cases | Coverage |
| --- | --- | --- | --- | ---: | --- |
| `REQ-RISCV-HARDEN-005` | `.spipe/simple_riscv_hardening/state.md` AC-5 | `test/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.spl` | `doc/06_spec/03_system/app/hardware/feature/simple_riscv_hardening_ac5_spec.md` | 4 | Positive, edge, error; runtime TEST_BLOCKED |

## Pass/fail criteria

PASS requires all four scenarios to execute with real assertions, exact
generator/golden equality, no stale marker, zero placeholders, current manual
mirror, and a blocker-free maintenance scan. Any missing file, stale marker,
mismatch, nonzero/signal exit, unadmitted runtime, or placeholder is failure.

## Manual rendering and capture policy

All four scenario narratives and literal `step("...")` flows remain visible.
Helper/source detail may be folded. Evidence uses linked text/log artifacts;
no screenshot or GUI capture applies to this RTL source/product contract.

## Current status

`TEST_BLOCKED` on 2026-08-16: the admitted Stage-2 compiler strictly built the
generator, but its artifact exited 132 with `invalid field receiver`. No
admitted full CLI was available, so runtime, docgen, and `sspec-maintain` were
not run.
