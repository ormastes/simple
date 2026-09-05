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

The original foundation slice excluded scalar execution. The user's subsequent
mission-critical Gen2 implementation request explicitly expands this active
lane with the following requirements; it does not retroactively qualify the
foundation evidence:

- REQ-G2-012: Materialize one typed scalar completion protocol and exactly one
  architectural retirement owner. ALU, control, and LSU providers must hold a
  complete normalized payload until atomic acceptance, preserve event identity,
  aggregate implementation faults, and never source architectural order.
- REQ-G2-013: Materialize the declarative M/Zmmul provider without runtime
  XLEN or provider selection. The projection must bind the concrete instruction,
  registers, operation, profile, provider, RV32/RV64 width, and structural
  receipt; Zmmul must reject divide/remainder. The iterative owner must hold
  completion under backpressure and implement division-by-zero, signed overflow,
  high-half signedness, and RV64 W-result rules exactly.
- REQ-G2-014: Materialize ECALL and EBREAK as real scalar execution providers.
  ECALL must select architectural causes 8/9/11 from the accepted U/S/M
  privilege, EBREAK must select cause 3, both must suppress register/memory/
  redirect effects, and both must enter the same atomic trap and sole-retirement
  path as every other scalar provider. Reserved privilege encoding 2 must fail
  closed as illegal instruction with the original instruction in `tval`.
- REQ-G2-015: Complete the shared scalar-I integer execution projection for
  RV32/RV64 upper-immediate, comparison, logical/arithmetic shift, and RV64
  word-result rows. Register shift counts must be masked architecturally,
  arithmetic shift must preserve sign, and every RV64 word result must be
  truncated to 32 bits then sign-extended exactly once.
- REQ-G2-016: Materialize a typed, fail-closed Zicsr access projection for all
  six CSR instruction forms. The projection must bind the concrete instruction,
  CSR address, register operand, privilege class, read-only class, and external
  CSR-bank presence/read value before producing read/write intent. It must
  preserve CSRRW `rd=x0` read suppression, CSRRS/CSRRC zero-source write
  suppression, immediate semantics, and illegal-instruction cause/tval on
  absent, underprivileged, reserved-class, read-only-write, or register-binding
  failure. This projection is not Zicsr product support until a stateful atomic
  CSR owner is composed through the sole-retirement path.
- REQ-G2-017: Materialize exact `FENCE` and `FENCE.I` rows as a one-entry typed
  accepted-effect owner. It must preserve `fm`/`pred`/`succ`, require an
  explicit ordering or instruction-stream-invalidation acknowledgement before
  retirement, hold effect and completion under backpressure, reject reserved
  encodings, and never issue an effect for illegal or identity-mismatched
  events. `FENCE.I` remains gated by the explicit `Zifencei` product profile.

Still out of scope for this foundation document: complete profile compliance,
PPA qualification, MMU/Linux, Debug 1.0, trace, vector, dual issue, and OoO.
