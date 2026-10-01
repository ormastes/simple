# RISC-V Gen2 precise system exceptions

Status: development evidence; qualification requires the admitted self-hosted compiler and the generated-product GHDL gate.

## Scenario: exact ECALL and EBREAK projections

1. Build concrete RV32 ECALL and RV64 EBREAK projections.
2. Verify their semantic origins and strict HWIR shape.
3. Confirm arithmetic instructions fail the exact system-provider scope.

## Scenario: closed precise-retirement product

1. Compose an RV64 ECALL product.
2. Require the system provider, registered completion skid, arbitration/trap path, one retirement owner, and fault aggregation.
3. Emit strict VHDL and verify those compiler-owned entities are present.

## Behavioral evidence gate

`test/02_integration/compiler/riscv_scalar_system_cycle_ghdl_spec.spl`
generates complete RV32 ECALL and EBREAK scalar products. It holds architectural
retirement backpressure, checks the trap/cause/tval payload and internally
assigned first order, then accepts the record and proves it is not duplicated.
This gate must run with an admitted self-hosted compiler before qualification.

Traceability: REQ-G2-012, REQ-G2-014, NFR-G2-015.
