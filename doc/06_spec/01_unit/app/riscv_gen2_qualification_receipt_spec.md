# RISC-V Gen2 qualification receipt contract

Executable companion: `test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl`.

This is a **planned qualification receipt** contract. It does not mean that a
Gen2 receipt has been retained or that a target has qualified.

The Pure-Simple writer accepts one exactly-shaped, runner-produced manifest:

- exactly two rows, ordered RV32 then RV64;
- the fixed product `riscv-gen2-zca-trap-single-outstanding-v3`, bound to
  `rv32-zca-cjal-critical` / `riscv-gen2-rv32-zca-cjal-critical` for RV32 and
  `rv64-zca-addiw-critical` / `riscv-gen2-rv64-zca-addiw-critical` for RV64;
- a hash-bound product command/zero exit, `.gen.json`, generated VHDL, and
  behavioral testbench for every row;
- separate hash-bound GHDL analyze, elaborate, and run commands, zero exits,
  and logs for every row;
- source, config, and graph identity SHA-256 values for every row;
- an admitted Stage-4 `pure-simple-full-cli`, its provenance envelope, and its
  source revision; and
- measured `branch` coverage with the canonical 8,000 basis-point (80%)
  threshold or higher, including its command/report, exact changed-file list,
  and explicit generated-VHDL/testbench/legacy/retirement-owner exclusions.

The writer never invokes GHDL or a test command and never creates a command
result. It binds supplied files with no-follow regular-file checks and SHA-256,
retains copies under the fresh relative directory
`build/evidence/riscv_gen2_hwir_foundation/<run-id>/`, checks the inputs again,
and writes `qualification_receipt.json` last. Reusing a run directory, a
missing/changed input, nonzero exit, incomplete row, unknown manifest field, or
unadmitted compiler provenance fails closed.

An admitted Stage-4 CLI invokes the writer source with exactly
`--manifest <relative-manifest-path> --run-id <safe-run-id>`. There is no
evidence-emission switch: a runner must first create the complete manifest from
its command-owned results outside the final receipt directory.

The executable companion verifies exact v2 parsing, fixed row ordering,
coverage/list bindings, command/testbench/GHDL exits, duplicate and missing
fields, and nested receipt rendering. It remains source-level acceptance until
the admitted runtime executes it; mocked GHDL or a static shell-token scan does
not produce qualification evidence. Writer-level acceptance is still pending
for exact command grammar, duplicate-safe product JSON, canonical parent and
no-symlink handling, complete retained-destination rehash, source/destination
mutation, and failure cleanup. Parser-only examples do not prove those claims.
