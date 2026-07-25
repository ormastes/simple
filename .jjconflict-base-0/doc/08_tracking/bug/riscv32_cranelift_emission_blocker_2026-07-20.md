# Bug: RISC-V 32 (rv32) — no native-build emission path; serial shell unverifiable

**ID:** riscv32-cranelift-emission-blocker-2026-07-20
**Domain:** compiler/backend, os/simpleos
**Severity:** blocker (for the rv32 boot→login→ls goal)
**Filed:** 2026-07-20

## Summary

The rv32 serial management shell (login via `SshUserDb`, `ls` via
`g_vfs_readdir`, `launch` via `fs_exec_spawn`) is **implemented and committed**
in `src/os/kernel/arch/riscv32/{boot,console,shell_lite}.spl`, but there is no
`native-build` path that emits a bootable rv32 baremetal ELF, so the rv32
boot→login→ls→launch flow cannot be QEMU-verified. rv64 has a working cranelift
emission path (`--target riscv64-unknown-none`); rv32 does not.

## Evidence

- `src/compiler/70.backend/backend/llvm_capability.spl:626` reports:
  `"riscv32 hosted: UNSUPPORTED (use riscv32-unknown-none-elf)"`.
- `src/compiler/70.backend/backend/llvm_cross_target.spl:345` install hint:
  `"Hosted RISC-V32 is unsupported; use riscv32-unknown-none-elf"`.
- `src/compiler/70.backend/backend/llvm_native_link.spl:1483` recognises
  `riscv32-unknown-none` / `-none-elf` triples for linking, but no cranelift
  rv32 codegen emits the kernel image (rv64 uses
  `examples/09_embedded/simple_os/arch/riscv64/linker.ld` +
  `--target riscv64-unknown-none` per
  `scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1:307`; no rv32
  analogue exists).
- rv32 is M-mode baremetal (no OpenSBI handoff), so it additionally needs an
  M-mode entry/crt0 + its own linker script; neither is present under
  `examples/09_embedded/simple_os/arch/riscv32/`.

## Impact

- rv32 boot→login→ls→launch cannot be built or booted. rv64 is unblocked.
- The rv32 shell source is correct and compiles in the interpreter's import
  resolution (modulo the pre-existing, interpreter-only `Fat32Core` semantic
  quirk that also affects rv64 and is NOT a codegen blocker).

## Ready (unblock-on-emission)

`src/os/kernel/arch/riscv32/console.spl` (`serial_shell_main`,
`_serial_login` via `sshd_create_default_users`, `_shell_ls` via
`g_vfs_readdir`, `_shell_launch` via `fs_exec_spawn`), `shell_lite.spl`
(`rv32_shell_dispatch`, `rv32_shell_format_dir_entries`), `boot.spl`
(`if os_main(): serial_shell_main(0)`). `_bytes_to_text` notes that the rv32
freestanding runtime must also export `rt_string_from_byte_array` (linked on
rv64 in `freestanding_runtime.c`).

## Fix direction

1. Add a cranelift rv32 codegen path (or llvm `riscv32-unknown-none-elf` emit
   for baremetal) + an M-mode crt0/entry + `arch/riscv32/linker.ld`.
2. Mirror the rv64 `native-build` invocation (`ps1:307`) for `--target
   riscv32-unknown-none-elf`.
3. Ensure the rv32 freestanding runtime exports `rt_string_from_byte_array`.

## Related

- rv64 serial shell + login + ls: commit 6b87d996bf62
- rv64+rv32 launch command: commits cc5256812d48 / 8ef6c4c8a11a
