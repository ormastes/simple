# RV32 GHDL Expected SATP Policy Contract

Source: `test/01_unit/os/kernel/arch/rv32_ghdl_satp_policy_contract_spec.spl`

Evidence class: `source-contract`.

The spec pins the GHDL Linux acceptance payload's branchless Pure Simple zero
receipt, its telemetry consumer, and removal of the former C runtime query and
active inventory entries. It does not claim a live `satp` CSR read or runtime
MC/DC evidence.
