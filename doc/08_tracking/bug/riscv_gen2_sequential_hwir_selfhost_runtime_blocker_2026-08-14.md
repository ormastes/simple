## Triage 2026-08-17 — BLOCKED, skipped fast (not a compiler/runtime/tooling defect)

Blocker: requires a provenance-admitted self-hosted Stage-4 CLI whose bounded
test-ABI probe passes. `bin/simple` in this lane is still the Rust seed (it
prints the seed warning banner), and this lane is forbidden from building the
main compiler. Unblock = deploy Stage-4, then run the exact resume commands from
`.spipe/riscv_gen2_hwir_foundation/state.md`. Unchanged.
# RISC-V Gen2 Sequential HWIR Self-Host Runtime Blocker

Status: open

Owner: compiler/bootstrap runtime owner; final reviewer `/root`.

## Failure

On 2026-08-14, `bin/release/simple test
test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl
--mode=interpreter` failed before test execution because the wrapper's bounded
test-ABI probe rejected
`release/x86_64-unknown-linux-gnu/simple`. Direct execution of that deployed
self-hosted binary for `check src/compiler/50.mir/hwir/sequential.spl` exited
139 after printing the check banner; `bin/simple_native test ...` also exited
139 without output. The expected canonical `bin/simple` entry is absent.

Affected acceptance: REQ-G2-004, NFR-G2-001/003/011, A13 focused execution, lint,
duplicate-check, `sspec-maintain`, branch coverage, compiler/core regression,
and independent generated-VHDL/GHDL evidence.

## Unblock condition

Deploy a provenance-admitted self-hosted Stage-4 CLI whose bounded test ABI
probe passes. Then run each exact resume command once from
`.spipe/riscv_gen2_hwir_foundation/state.md`, retain the command outputs and
coverage report, and update the canonical plan. Do not use the Rust seed or a
Stage-2 compiler as qualification evidence.

## Source locations

- `src/compiler/50.mir/hwir/sequential.spl`
- `src/compiler/70.backend/backend/hwir_to_vhdl.spl`
- `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`
