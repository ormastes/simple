# RISC-V Gen2 exhaustive target-trap parcel oracle

Executable companion: `test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl`.

## Purpose

The oracle executes the typed `strict_zca_target_trap_migrating_predecode_hwir`
graph directly for each of the 65,536 possible 16-bit parcels, once for the
RV32 C.JAL critical product and once for the RV64 C.ADDIW critical product.
It deliberately does not use a second decoder or classifier as an oracle.

## Evidence steps

1. Prepare two independent, validated slot-scheduled host evaluators for the
   concrete product graph.
2. Supply the same parcel, PC, register index, and register value to both
   evaluators for every parcel in ascending order.
3. Require their full output tuples and ordered digests to be identical.
4. Check the closed output partition for every tuple:
   illegal values fail closed; normal legal values have a canonical instruction
   and correct redirect/fall-through relationship; C.EBREAK is the sole trap
   and has canonical EBREAK, cause 3, and zero `tval`.
5. Require complete coverage, non-empty legal and illegal partitions, and
   exactly one trap parcel for each product.

The test traces REQ-G2-002, REQ-G2-010, REQ-G2-011, NFR-G2-010, and
NFR-G2-012. Its qualification result must be recorded with the self-hosted
critical-mode evidence; bootstrap-only execution is diagnostic evidence only.
