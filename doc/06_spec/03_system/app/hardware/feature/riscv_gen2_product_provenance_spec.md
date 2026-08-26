# RISC-V Gen2 Typed Product Provenance — System Scenario

This scenario calls direct compiler APIs for compiler-owned, source-less typed
frontend products before HDL simulation. It does not certify RTL behavior, a
processor, or target equivalence: the self-hosted RV32/RV64 VHDL/GHDL lane
remains required for that evidence.

## Closure-bound RV32 stateful product

The scenario emits the RV32 one-entry frontend through a direct compiler API
from its typed sequential plan. It verifies the strict route, 64-character closure hash, the
same hash in the emitted VHDL header, complete concrete configuration, public
port contract, decoder identity/digest, origins, and stable state/rule lineage
anchors.

## Closure-bound RV64 trap product

The scenario emits the RV64 trap-stateful frontend through a direct compiler
API and verifies its distinct strict route, nonempty closure hash, matching VHDL header, complete concrete
configuration, public port contract, decoder identity/digest, origins, and
trap-output lineage anchor. This is development-stage provenance evidence, not
release qualification.

## Target-specific trap products

The scenario renders the closed RV32 C.JAL and RV64 C.ADDIW trap products
through direct compiler APIs. It checks each product's concrete critical profile, nonempty closure hash, and
only its corresponding migrating decoder. It explicitly rejects the reciprocal
decoder from each emitted VHDL payload. This is direct-API compiler-provenance
coverage; the planned self-hosted RV32/RV64 VHDL/GHDL receipt remains mandatory
before any RTL, target-equivalence, or release claim.

## Traceability

- REQ-G2-009: compiler-owned specialized products retain concrete critical
  identity and do not mix the RV32 C.JAL and RV64 C.ADDIW decoder closures.
- REQ-G2-010: typed stateful output is bound to an explicit closure graph and
  never falls back to a legacy textual VHDL path.
- NFR-G2-010/NFR-G2-011: emitted provenance records concrete target/profile,
  typed closure, and stateful decoder selection without a fabricated source
  closure or runtime XLEN selection.
