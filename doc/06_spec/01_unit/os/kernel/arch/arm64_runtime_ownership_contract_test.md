# ARM64 Runtime Ownership Contract

Source: `test/01_unit/os/kernel/arch/arm64_runtime_ownership_contract_test.shs`

Evidence class: `source-contract`.

## Checks

- ARM64 runtime symbols have one production owner rather than competing weak
  stubs.
- per-CPU atomic state is reached through its architecture owner.
- VFS and server boot paths do not acquire private copies of runtime ownership.

Run with `sh test/01_unit/os/kernel/arch/arm64_runtime_ownership_contract_test.shs`.
The result is structural evidence; ARM64 QEMU boot remains the live-guest gate.

