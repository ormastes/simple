# Concrete RISC-V Scalar Elaboration

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_riscv_scalar_core_spec.spl`

## Purpose and scope

This focused source-level unit specification exercises the scalar elaboration
descriptor for concrete RV32 and RV64 configurations. It verifies descriptor
identity, ISA/profile provider admission, physical-address-width identity, and
dispatch through the selected scalar table.

## Scenarios

1. Elaborate separate concrete RV32 and RV64 scalar products.
2. Reject a provider that is incompatible with the selected ISA profile.
3. Distinguish otherwise similar products by their concrete configuration.
4. Dispatch selected base-I and M-table instruction rows.

## Requirement traceability

- REQ-G2-002 — concrete typed RV32/RV64 configuration and ISA-profile choices
  are validated at elaboration.

## Evidence boundary

This is scalar descriptor and dispatch-table source evidence only. It does not
execute scalar instructions in a pipeline, construct register or memory state,
emit or simulate RTL, establish full ISA coverage, or qualify a hardware
implementation.
