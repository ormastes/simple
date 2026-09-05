# RISC-V Gen2 atomic CSR owner is missing

Date: 2026-08-12
Status: implementation complete; qualification open
Owner: RISC-V Gen2 HWIR scalar execution

## Finding

`src/compiler/50.mir/hwir/riscv_scalar_csr_projection.spl` provides the typed,
fail-closed access calculation. `riscv_scalar_csr_owner.spl` now captures its
full completion and write intent, validates event/instruction/length/rd identity,
holds state under backpressure, and asserts the CSR commit only with accepted
completion. Scalar product composition admits the stateful CSR provider.

Treating the stateless projection as a complete provider would allow an external
CSR write to occur independently of completion acceptance or retirement
backpressure. That is not mission-critical-safe and must remain rejected.

## Remaining unblock condition

Qualify the implemented typed sequential CSR owner with an admitted self-hosted
compiler and generated VHDL/GHDL cycle evidence that proves it:

- captures the frozen CSR address, operation, source, privilege, instruction,
  event identity, and full scalar completion envelope;
- performs exactly one accepted CSR-bank transaction and holds its response;
- suppresses every CSR write on privilege, presence, read-only, identity, or
  protocol failure;
- commits the write atomically with the accepted scalar event through the
  existing arbitration, trap normalizer, and sole retirement owner;
- exposes a sticky protocol fault and has generated RV32/RV64 GHDL cycle tests
  for backpressure, reset, duplicate/rogue response, and one-write behavior.

Only after those checks pass may the Gen2 product advertise Zicsr capability.
