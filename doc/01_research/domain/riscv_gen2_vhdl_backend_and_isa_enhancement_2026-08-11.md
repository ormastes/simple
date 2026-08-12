# Simple VHDL Backend and RISC-V Gen2: Research, Architecture, and Development Plan

Date: 2026-08-11
Status: proposed and partially implemented
Extends: `riscv_gen2_production_audit_2026-07-27.md` and `riscv_gen2_production_roadmap_2026-07-27.md`

## Provenance and verification status

This is a forward-looking architecture decision, not a claim that Simple has a
complete RISC-V profile. V1 cores and direct VHDL remain supported legacy
products. The Gen2 critical route is fail-closed: unsupported hardware MIR is
rejected before legacy VHDL emission. Each advertised compressed row requires
typed HWIR, a real-MIR intrinsic, generated VHDL simulation, and manifest evidence.

## Executive recommendation

```text
declarative RISC-V semantics + type-parameterized core + compile-time providers
    -> typed HWIR + graph aspects + proof-carrying PPA transforms
    -> target legalization -> deterministic VHDL-2008 serializer
```

VHDL is the conservative serializer, not the place for feature selection,
debug insertion, width specialization, pipeline choices, or optimization.

## Multi-level HWIR

1. **Elaboration HWIR** resolves `CoreConfig`, XLEN, address widths, providers,
   capabilities, and aspect plan into concrete products.
2. **RTL HWIR** models typed combinational values, registers, memories,
   channels, clocks/resets, effects, and pipeline boundaries.
3. **Target HWIR** legalizes generic operations to FPGA/ASIC resources before
   deterministic VHDL emission.

`HwNodeId` and origin sets survive every stage into VHDL and synthesis reports,
supporting source waves, first-divergence analysis, and PPA/aspect provenance.

## Compile-time aspects

Hardware aspects are compiler-host discovered, hash-pinned graph transforms;
there is no runtime RTL dynamic loading. Manifests declare stage, capabilities,
join points, effect class, ordering, ports/state, latency/throughput contract,
and proof obligations. Supported advice is `observe`, `attach`, `before`,
`after`, `wrap`, `replace`, and `verify`.

Observational aspects require architectural noninterference. Timing-changing
aspects require transaction/retirement equivalence. An absent aspect emits zero
ports, state, logic, routing, and unresolved references.

## RV32/RV64 unification and ISA database

One source elaborates into separate RV32/RV64 products. XLEN is never a runtime
datapath input. `CoreConfig` selects concrete providers and hardware types.
The ISA database describes each encoding, legality, operands, semantic operation,
effects, traps, compressed aliases, tooling metadata, and verification hook once.
Separate netlists may deliberately differ when ISA canonicalization requires it.

## Compressed ISA plan

Fetch operates on 16-bit parcels regardless of XLEN and preserves original bits,
length, canonical instruction, legality reason, fetch PC, and next PC through
retirement. Zca comes first, then Zcb and product-selected Zcmp/Zcmt/FP overlays.
The 65,536 parcel space permits exhaustive classification/decompression checks.
Assembler, disassembler, compiler selection, linker relaxation, ELF attributes,
documentation, and tests use the same ISA data.

The current mission-critical route proves individual Zca rows only. Manifest
fields `target_rtl_equivalence_verified` and `advertises_extension` remain false
until a complete selected subset has independent evidence.

## PPA, debug, and verification

After specialization: structural DCE, range/width inference, decode/mux
factoring, memory inference, resource binding, operand isolation, retiming,
elastic-buffer placement, and proven rewrites. Every semantic pass needs
reset/output/retirement equivalence; timing changes need transaction equivalence
and declared latency.

Freeze `RetireRecord` before performance work. Verification combines Sail,
RVFI/riscv-formal, riscv-dv, profile tests, mutation tests, and board evidence.
Debug 1.0 and E-Trace become typed aspects over fetch/decode/execute/LSU/commit
join points, with published area/Fmax/power deltas and source maps from HWIR.

## Product and parallel sequence

1. Legacy evidence and core-only PPA baselines.
2. HWIR parity, strict routing, origins, and aspect manifests.
3. Unified precise-retirement scalar core and ISA database.
4. Parcel front end and complete selected compressed subsets.
5. Single-issue PPA pipeline, memory providers, A/RVWMO, PMP/PMA, MMU/Linux.
6. Debug/trace/safety, then separate dual-issue, vector, OoO, and multicore lanes.

Frozen parallel interfaces: `HwNodeId`, `HwOrigin`, `HwType`, `HwModule`,
`HwMemory`, `HwChannel`, `CapabilityManifest`, `AspectManifest`, `CoreConfig`,
`IsaEntry`, `PredecodedInstruction`, `DecodedUop`, `RetireRecord`, fetch/LSU
contracts, target profiles, and QoR records. Architecture owns schema versioning;
implementers consume tagged contracts and never edit generated VHDL.

## Non-goals and immediate gate

Reject runtime extension/aspect lookup, raw VHDL from aspects, string-level
semantic transforms, host `i64` as generic hardware bits, duplicated RV32/RV64
semantics, optimization without proof, and unproven profile claims.

The immediate gate is explicit: critical `rv32`/`rv64` Gen2 targets lower only
through strict HWIR; unsupported hardware produces stable `HWIR-E-*` diagnostics
and cannot emit direct-builder artifacts.

## References

- CIRCT: https://circt.llvm.org/docs/Dialects/
- RISC-V C: https://docs.riscv.org/reference/isa/v20260120/unpriv/c-st-ext.html
- RISC-V Zc: https://docs.riscv.org/reference/isa/unpriv/zc.html
- RISC-V Debug: https://docs.riscv.org/reference/debug/introduction.html
- RISC-V E-Trace: https://docs.riscv.org/reference/e-trace/v2.0/index.html
- Local evidence: `doc/01_research/local/riscv_gen2_hwir_foundation.md`
