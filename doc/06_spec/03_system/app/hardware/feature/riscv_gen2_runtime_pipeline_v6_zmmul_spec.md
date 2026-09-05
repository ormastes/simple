# RISC-V Gen2 V6 Flattened Zmmul Runtime Pipeline

Status: development evidence; self-hosted qualification remains pending.

This executable system scenario covers the public V6 flattened runtime pipeline
for the deliberately narrow `rv32i_zmmul` and `rv64i_zmmul` profiles. It does
not claim an IM implementation: DIV/REM remain rejected until V7 supplies one
unified runtime-M owner.

## Scenarios

1. Elaborate RV32 and RV64 V6 products. Each has the fixed 61-port public
   contract, exactly one dynamic `muldiv` owner, and one V6 class router.
2. Trace the tag-two protocol end-to-end: pending-owner request valid/tag,
   request acceptance, completion valid/readiness, and the provider fault into
   the V6 global fault gate.
3. Compile the same RV32 product twice through
   `hwir-gen2-scalar-runtime-pipeline-v6-flat-direct`; require an identical
   graph digest and VHDL text, including the V6 receipt and flattened muldiv
   instance.
4. Try an RV32IM configuration and require elaboration failure. This makes the
   Zmmul boundary explicit instead of accepting legal DIV/REM instructions with
   an incomplete provider.

The companion integration scenario
`test/02_integration/compiler/riscv_scalar_runtime_pipeline_v6_flat_clocked_ghdl_spec.spl`
is the cycle-level VHDL/GHDL evidence lane for multiply latency, held completion,
lineage, and protocol fault behavior. Neither this structural scenario nor a
bootstrap runner result is self-hosted qualification evidence.
