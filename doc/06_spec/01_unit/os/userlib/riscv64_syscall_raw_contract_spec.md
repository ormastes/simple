# RISC-V64 raw syscall ABI contract

Mirror of `test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl`.

The executable SSpec checks raw syscalls route through the architecture `ecall` shim, CSR and SBI operands use architecture-runtime cases, and startup remains outside the RISC-V package closure while CMO operands route through runtime ownership.

This is static ABI routing evidence and does not run the calls on RISC-V hardware.
