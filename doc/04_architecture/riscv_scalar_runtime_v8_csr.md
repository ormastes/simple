<!-- codex-architecture -->
# Runtime scalar pipeline V8: combined Zmmul and Zicsr CSR owner

## Status

Implemented at source level.  Qualification is **BLOCKED**: no admitted
self-hosted Simple runtime has yet run the V8 structural and clocked-GHDL
evidence lanes.  Bootstrap-seed output is development evidence only and must
not be promoted to a PASS or release claim.

## Decision

V8 is a direct-child, flattened scalar-runtime product for exactly
`rv32i_zmmul_zicsr_zifencei` and `rv64i_zmmul_zicsr_zifencei`.  It retains the
V6 multiply provider and adds one dynamic CSR owner; it deliberately excludes
the IM profiles and therefore every DIV/REM semantic.  A future IM product
requires a single unified dynamic M provider rather than a second tag-two
owner.

The public composition is
`riscv_scalar_runtime_pipeline_v8_flat.spl`.  It connects the tag-two
Zmmul provider, tag-three CSR provider, existing LSU/FENCE owners, V8 class
router, completion machinery, and `riscv_scalar_runtime_global_fault_gate_v8`.
`riscv_scalar_runtime_pipeline_v8_flat_to_vhdl.spl` is the sole strict VHDL
lowering route.  The V8 router reserves class 6/tag 3 for CSR work; class 6
and effect 3 are exact decoder-plan metadata, not compatible aliases.

## CSR ownership and capture

`riscv_scalar_runtime_csr_provider.spl` is the one-entry sequential tag-three
owner.  Its plan-bound admission/projection validates the full decoded request
record before capture: tag, legal/illegal state, canonical/original identity,
length, PC/fallthrough, event and lineage identity, raw rd/rs1/rs2 fields,
and the exact row/form/semantic/class/effect/width values from the canonical
decoder plan.  A malformed tag-three request sets the sticky protocol fault;
it does not access or commit a CSR.

On request acceptance the provider captures `csr_present`, `csr_read_value`,
policy outcome, normalized completion fields, and legal commit intent.  It
never rereads the live CSR service while the completion is held.  Lookup uses
the frozen 12-bit address interface.  Commit is asserted only when the held
completion is consumed (`completion_ready`) and its captured legal-write
intent is set, which gives exact-once commit under backpressure.

The six admitted forms are CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, and CSRRCI.
RS1 x0 is normalized to zero; rd x0 suppresses architectural writeback only.
Absent CSR, insufficient/reserved privilege, and a read-only write request are
execute-trap outcomes (cause 2, original instruction tval), not decoder-illegal
or provider-protocol faults.  No CSR policy failure commits.

## Requirement and evidence boundary

The structural system specification maps this product to `REQ-G2-013`,
`REQ-G2-016`, and deterministic-lowering `NFR-G2-003` at
`test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl`.
It covers combined RV32/RV64 construction, class-6/tag-3 topology, the CSR
service ABI, deterministic VHDL, and rejection of standalone Zicsr and IM.
The clocked behavioral lane is
`test/02_integration/compiler/riscv_scalar_runtime_pipeline_v8_flat_clocked_ghdl_spec.spl`.

## Qualification prerequisite and resume

**BLOCKED prerequisite:** deploy/select an admitted pure-Simple self-hosted
binary at `bin/release/x86_64-unknown-linux-gnu/simple` (not `bin/simple` when
it resolves to the Rust bootstrap seed), with GHDL installed and callable.
After that prerequisite is true, resume with these commands, in order:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/compiler/riscv_scalar_runtime_pipeline_v8_flat_clocked_ghdl_spec.spl --mode=interpreter
```

Only successful admitted-runtime execution of both lanes can change this
document's status; no release PASS is claimed here.
