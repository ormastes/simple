# `ghdl_validate_rv32 --analyze` gate is blind to a semantically broken generated CPU

- **Filed:** 2026-07-28
- **Severity:** high — this is the fake-CPU evidence class that `check-riscv-rtl-truth.shs` exists to prevent
- **Status:** open
- **Found via:** Lane R3 gate-honesty audit (`doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-28.md` §3)

## Symptom

`check-riscv-hardware-gates.shs` counts `ghdl_validate_rv32 --analyze` as one of
its 22 hardware gates. A green there reads as "the generated RV32 CPU is
validated". It is not: `--analyze` runs `ghdl -a` only and `exit 0`s before
elaboration or simulation (`scripts/fpga/ghdl_validate_rv32.shs`, the
`[ "$PHASE" = "--analyze" ] && exit 0` line). It proves the generated VHDL
*parses*. It asserts nothing about behaviour.

## Injection evidence (exit codes captured without a pipe)

Run against a private copy of `build/vhdl/rv32` so the shared tree was untouched.

| Injected defect | Expected | Observed exit |
|---|---|---|
| (a) semantic: instruction-fetch increment `idxp1 := pc_idx + 1` -> `+ 2` in `rv32_exec_core.vhd` (valid VHDL, broken CPU) | should fail | **0 — PASS** |
| (b) syntax error on the same line | should fail | 1 |
| (c) required `rv32i_decode.vhd` removed | should fail | 1 |

(a) is the finding: a generated core that fetches every other instruction still
passes the gate. (b) and (c) confirm the gate does fail on what it actually
claims (analysis + file presence), so it is **weak/mis-scoped, not vacuous**.

## Why it matters

`check-riscv-rtl-truth.shs` was written because an empty architecture, a
`smoke_handoff` step-counter "core", a decode-free core, and a wrapper
instantiating an undefined entity have all shipped as evidence before. Every one
of those would pass `--analyze`. This gate cannot distinguish a real CPU from a
syntactically valid non-CPU.

## Suggested fix

The same script already implements elaborate + run under its non-`--analyze`
phase. Either invoke that phase from the hardware-gates entrypoint, or rename
the gate to `ghdl_analyze_rv32 (syntax only)` and stop counting it toward a
hardware claim. Do not leave it counted as-is under its current name.
