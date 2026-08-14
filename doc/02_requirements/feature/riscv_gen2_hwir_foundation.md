# RISC-V Gen2 HWIR Foundation — Feature Requirements

Selected by user request on 2026-08-11.

- REQ-G2-001: Define typed, versioned HWIR module/node/origin contracts for the
  first strict hardware-emission slice.
- REQ-G2-002: Define and validate an elaboration-time `CoreConfig` that accepts
  concrete RV32 and RV64 products with explicit ISA and compressed-decode
  profiles, and rejects invalid XLEN/configuration or incompatible profiles.
- REQ-G2-003: Strict HWIR lowering accepts only explicit supported hardware
  input and fails with a diagnostic rather than falling back to legacy VHDL.
- REQ-G2-004: Strict emission renders deterministic, non-empty VHDL-2008 for a
  supported typed combinational module and preserves stable source lineage.
- REQ-G2-005: The legacy V1 route remains explicit and is never invoked by a
  strict Gen2 request.
- REQ-G2-006: A critical hardware build snapshots typed assurance policy,
  requires an explicit RV32/RV64 target, and records the strict HWIR route and
  concrete configuration in its artifact provenance.
- REQ-G2-007: Provide a shared width-neutral compressed-parcel semantic
  boundary with deterministic legal/illegal classification and canonical
  C.EBREAK/C.NOP/C.ADDI behavior; legacy core adapters migrate separately.
- REQ-G2-008: Establish a declarative ISA capability table for the verified
  critical compressed subset and derive its host-side capability manifest from
  that table without placing metadata dispatch in RTL.
- REQ-G2-009: Provide a source-less, compiler-owned critical product entry for
  the bounded Zca control-predecode slice. It must reject source mixing, wrong
  concrete target, non-critical policy, and AOP contamination before artifact
  cleanup; its provenance must explicitly state that there is no user source
  closure.
- REQ-G2-010: Provide a typed, single-outstanding stateful parcel frontend
  product that captures the fetched parcel, PC, and branch-read pair, preserves
  them through dispatch, and accepts no new fetch until matching retirement.
  Early, stale, or mismatched retirement must become a reset-cleared sticky
  protocol fault.
- REQ-G2-011: Before a non-control compressed row may enter a composed
  frontend, normalize it to an explicit typed outcome with legality derived
  from its classifier and reserved-encoding gates—not from a sentinel
  canonical instruction value.

Out of scope: scalar pipeline, complete ISA/Zc decode, aspect execution, PPA
rewrites, MMU/Linux, Debug 1.0, trace, vector, dual issue, and OoO.

## Related artifacts

- NFR requirements: `doc/02_requirements/nfr/riscv_gen2_hwir_foundation.md`
- Parallel execution plan: `doc/03_plan/agent_tasks/riscv_gen2_hwir_foundation.md`
- Qualification test plan: `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- Architecture: `doc/04_architecture/riscv_gen2_hwir_foundation.md`
- Detail design: `doc/05_design/riscv_gen2_hwir_foundation.md`
- System-scenario manual:
  `doc/06_spec/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.md`
- SPipe state: `.spipe/riscv_gen2_hwir_foundation/state.md`
