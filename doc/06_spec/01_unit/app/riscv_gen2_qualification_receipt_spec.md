# RISC-V Gen2 qualification receipt contract

Executable companion: \`test/01_unit/app/riscv_gen2_qualification_receipt_spec.spl\`.

This is a **planned qualification receipt** contract. It does not mean that a
Gen2 receipt has been retained or that a target has qualified.

The Pure-Simple writer accepts one exactly-shaped, runner-produced manifest:

- exactly two rows, ordered RV32 then RV64;
- a zero exit plus generated VHDL, GHDL analyze, elaborate, and run log path
  and SHA-256 for every row;
- source, config, and graph identity SHA-256 values for every row;
- an admitted Stage-4 \`pure-simple-full-cli\`, its provenance envelope, and its
  source revision; and
- measured \`branch\` coverage with the canonical 8,000 basis-point (80%)
  threshold or higher.

The writer never invokes GHDL or a test command and never creates a command
result. It binds supplied files with no-follow regular-file checks and SHA-256,
retains copies under the fresh relative directory
\`build/evidence/riscv_gen2_hwir_foundation/<run-id>/\`, checks the inputs again,
and writes \`qualification_receipt.json\` last. Reusing a run directory, a
missing/changed input, nonzero exit, incomplete row, unknown manifest field, or
unadmitted compiler provenance fails closed.

