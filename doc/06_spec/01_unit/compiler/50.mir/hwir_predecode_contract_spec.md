# RISC-V Gen2 strict compressed-predecode contract

Executable companion:
`test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl`.

## Metadata

- Evidence class: typed-HWIR unit and deterministic VHDL-text contract.
- Profiles: Zca common-critical, RV32 C.JAL critical, and RV64 C.ADDIW
  critical.
- Requirements: REQ-G2-001, REQ-G2-002, REQ-G2-003, REQ-G2-004,
  REQ-G2-010, REQ-G2-011, NFR-G2-010, NFR-G2-011, and NFR-G2-012.

## Scenarios and evidence steps

1. **Strict structural admission.** Construct valid and duplicate-driver
   modules; require the valid shape to pass and the duplicate to fail before
   emission.
2. **Concrete RV32/RV64 specialization.** Admit C.JAL only in the RV32 C.JAL
   product and C.ADDIW only in the RV64 product; reject incompatible profiles
   and preserve the RV32 x1 link field.
3. **Target-trap closure.** Build the selected C.JAL and C.ADDIW trap decoders
   and frontends, require their closed row lists, one C.EBREAK entry, one
   overlap guard, and the exact typed decoder-child identity.
4. **Stateful frontend integrity.** Reject malformed public trap-retirement
   ports, decoder pins, output bindings, case-only names, sequential-rule
   changes, reset drift, decoder substitution, and public-port collisions.
   Require graph digests to change when their configuration, lineage, ports,
   decoder identity, or decoder digest changes.
5. **Configuration and interface fail-closed behavior.** Reject unsupported
   address widths, register counts, profile names, compressed profiles,
   malformed predecode/branch/trap interfaces, and non-critical construction
   before serialization.
6. **Typed control predecode.** Build C.J, C.BEQZ, C.BNEZ, C.JR, and C.JALR
   rows with concrete XLEN operand and physical-address widths; check their
   redirects, register-read pairing, and deterministic rendered form.
7. **Explicit normal outcomes.** Admit only classifier-complete non-control
   rows. Require every outcome to carry explicit legality, fall-through,
   redirect, and register/memory effect signals, with C.MV/C.ADD kept disjoint
   from JR/JALR/EBREAK boundaries.
8. **Frontend handoff contract.** Freeze the typed parcel-to-dispatch handoff
   for RV32 and RV64, including 16-bit parcel and 32-bit canonical instruction
   fields, concrete PC widths, dispatch ownership, and one-bit retirement
   ownership. Reject mismatched configuration and malformed ownership ports.
9. **Flat control composition.** Compose C.J/C.BEQZ/C.BNEZ into one
   critical-profile graph with exactly one driver for each public result, and
   reject construction outside the frozen profile.

## Evidence boundary

The companion is source-level elaboration, contract, and deterministic VHDL
text evidence. It does not constitute an independent simulation of emitted
RTL, exhaustive compressed-ISA qualification, or proof of a scalar pipeline or
architectural retirement effect. Self-hosted RV32/RV64 GHDL receipts, measured
coverage, and the typed architectural-producer integration remain required for
mission-critical release qualification.
