# RISC-V Gen2 typed CSR projection

Development-stage operator scenario for the typed RISC-V Gen2 Zicsr access
projection. This manual proves projection semantics only. It does not claim CSR
state ownership, product composition, generated-RTL equivalence, or Zicsr
qualification; those remain blocked by the atomic CSR owner.

## Elaborate one concrete CSR access for RV32 and RV64

1. Select the Zicsr-capable RV32 and RV64 product configurations.
2. Elaborate the same concrete CSRRW row without a runtime XLEN selector.
3. Confirm concrete XLEN values 32 and 64.

## Inspect the exact typed CSR state seam

1. Build the RV64 machine-status CSR projection.
2. Inspect the ungated `csr_lookup_address` output and `csr_present` /
   `csr_read_value` inputs; this ordering avoids a circular presence lookup.
3. Inspect `csr_read_enable`, `csr_write_enable`, `csr_address`, and
   `csr_write_value` outputs.

## Reject a read-only CSR write

1. Elaborate CSRRW against the read-only machine-vendor CSR.
2. Drive a present CSR from machine privilege with a matching source register.
3. Confirm illegal-instruction cause 2.
4. Confirm both CSR read and write effects remain zero.

## Hold completion and commit atomically

1. Build the sequential CSR owner around the frozen projection.
2. Confirm commit requires an occupied completion, downstream acceptance,
   captured write intent, a healthy protocol state, and no captured illegal or
   execute-trap event.
3. Compose the provider through arbitration, trap normalization, fault
   aggregation, and the sole retirement owner.
4. Confirm there is exactly one retirement owner and no binding gap.

## Evidence status

The executable scenario is
`test/03_system/app/hardware/feature/riscv_gen2_csr_projection_spec.spl` and
traces REQ-G2-016 / NFR-G2-017. This manual is maintained from the authored
scenario because no admitted full self-hosted SPipe/docgen CLI is currently
available. It must be regenerated and reviewed before qualification.
