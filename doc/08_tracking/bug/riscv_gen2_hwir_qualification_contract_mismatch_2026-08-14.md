# RISC-V Gen2 HWIR Qualification Contract Mismatch

Status: open

Owner: compiler evidence owner; final reviewer `/root`.

## Failure

`scripts/check/run-riscv-gen2-hwir-qualification.shs` invokes its composer with
`--emit-evidence` and `--compose-receipt`, and validates final schema
`simple-riscv-gen2-hwir-qualification-v1` with flat `status=pass` gate fields.
The in-tree Simple composer at
`src/app/test/riscv_gen2_qualification_receipt.spl` deliberately accepts only
`--manifest` and `--run-id`, identifies schema
`riscv-gen2-hwir-qualification-run-v1`, and writes its distinct retained-run
receipt structure. Its source explicitly states that it has no
`--emit-evidence` mode.

The static runner token contract test confirms only that the wrapper contains
the planned tokens; it cannot prove either phase is executable. No admitted
self-hosted runtime can satisfy this inconsistent command/schema contract.

## Selected contract (2026-08-14)

The shell runner owns phase-one command execution in a private staging sibling
while the final run directory remains absent. It runs the admitted CLI, measured
branch coverage, fixed testbench generation, and separate bounded GHDL analyze,
elaborate, and run commands. It then invokes the admitted CLI on the Simple
composer with only `--manifest` and `--run-id`. The composer exclusively
validates/copies evidence, creates the immutable final directory, and writes the
receipt last.

The schema advances to `riscv-gen2-hwir-qualification-run-v2`; v1 cannot meet
the selected NFR because it omits the coverage command, changed-file set,
exclusions, testbench identity, and individually bound GHDL commands/exits.
There is no accepted v1 retained receipt requiring compatibility.

## Unblock condition

Implement the selected contract, including exact-key parsing and deliberate-red
coverage for phase order, symlinks/preexisting paths, malformed/duplicate keys,
low coverage, each command failure, artifact mutation, composer failure, and
partial-receipt cleanup. Then execute it with an admitted Stage-4 CLI and retain
the receipt directory.

Relevant files:

- `scripts/check/run-riscv-gen2-hwir-qualification.shs`
- `src/app/test/riscv_gen2_qualification_receipt.spl`
- `test/01_unit/scripts/riscv_gen2_hwir_qualification_runner_contract_test.shs`
