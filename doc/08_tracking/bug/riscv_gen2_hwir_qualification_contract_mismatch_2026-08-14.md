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

## Unblock condition

Select one canonical two-phase design: a command-owned evidence producer must
run the fixed RV32/RV64 products and write hash-bound row artifacts, then the
Simple composer must consume only that validated manifest and write the final
receipt last. Align CLI switches, schemas, field names, filenames, and tests;
add deliberate-red contract coverage; then execute the wrapper with an admitted
Stage-4 CLI and retain the receipt directory.

Relevant files:

- `scripts/check/run-riscv-gen2-hwir-qualification.shs`
- `src/app/test/riscv_gen2_qualification_receipt.spl`
- `test/01_unit/scripts/riscv_gen2_hwir_qualification_runner_contract_test.shs`
