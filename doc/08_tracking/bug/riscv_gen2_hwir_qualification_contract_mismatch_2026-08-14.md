# RISC-V Gen2 HWIR Qualification Contract Mismatch

Status: implementation handoff; executable acceptance open

Owner: compiler evidence owner; final reviewer `/root`.

## Historical failure (superseded at source level)

The original `scripts/check/run-riscv-gen2-hwir-qualification.shs` invoked its composer with
`--emit-evidence` and `--compose-receipt`, and validates final schema
`simple-riscv-gen2-hwir-qualification-v1` with flat `status=pass` gate fields.
The in-tree Simple composer at
`src/app/test/riscv_gen2_qualification_receipt.spl` deliberately accepts only
`--manifest` and `--run-id`, identifies schema
`riscv-gen2-hwir-qualification-run-v1`, and writes its distinct retained-run
receipt structure. Its source explicitly states that it has no
`--emit-evidence` mode.

That v1 mismatch has been removed by the source-level v2 contract. This bug
remains open for the unverified authority and coverage gaps below, not because
the removed switches are still present.

The static runner token contract test confirms only that the wrapper contains
the planned tokens; it cannot prove either phase is executable. The current v2
source is aligned, but remains unexecuted and has the open authority gaps below.

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

The v2 source implementation now follows the selected contract and removes the
fictitious switches. This record remains open because the deployed runtime
cannot execute the Simple positive/deliberate-red suite or produce the admitted
RV32/RV64 GHDL receipt; static token checks are not closure evidence.

Highest-capability adversarial review additionally requires writer-level tests
for exact command content, duplicate-safe product-manifest parsing,
destination-side rehashing, canonical parent/no-symlink handling, and partial
run cleanup. Coverage now fails closed when any changed `.spl` file has no
decision inventory row and cross-checks the retained aggregate/list, but the
current runtime coverage format reports executed probes rather than an
independent static denominator. Therefore a missing branch cannot earn PASS;
the coverage producer must expose a complete zero-count decision inventory
before the 80% gate can close.

Resume after the admitted runtime and complete decision inventory exist:

`sh scripts/check/run-riscv-gen2-hwir-qualification.shs --stage4-cli <absolute-admitted-cli> --stage4-provenance <adjacent-provenance> --output-dir <absolute-fresh-run-dir>`

Relevant files:

- `scripts/check/run-riscv-gen2-hwir-qualification.shs`
- `src/app/test/riscv_gen2_qualification_receipt.spl`
- `test/01_unit/scripts/riscv_gen2_hwir_qualification_runner_contract_test.shs`
