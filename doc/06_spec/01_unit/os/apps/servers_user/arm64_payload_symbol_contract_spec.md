# ARM64 Server Payload Symbol Ownership Contract

Source: `test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl`

Evidence class: `source-contract`.

## Scenarios

- Use the sysroot-owned libc syscall trampoline and canonical public byte-array
  runtime ABI without introducing payload-local duplicate symbols.
- Keep byte addresses scoped to their consuming syscall and keep database
  traversal independent of unsupported array-enumeration lowering.
- Gate the final payload on emitted canonical secure-zeroization owners.

This contract checks source and emitted-symbol ownership; the ARM64 QEMU gate
provides live-guest evidence.

