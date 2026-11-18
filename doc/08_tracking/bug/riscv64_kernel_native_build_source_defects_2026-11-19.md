# riscv64 kernel native-build (LLVM) fails on four source defects

- id: riscv64_kernel_native_build_source_defects_2026-11-19
- status: verification-pending
- severity: P1 (blocks every riscv64 `--entry-closure` kernel build on the LLVM backend)
- found by: lane ssos-launch (riscv64 user-ELF launch), Linux seed built with `--features llvm`

## Symptom

`native-build --backend llvm --entry-closure --target riscv64-unknown-none` of
`examples/09_embedded/simple_os/arch/riscv64/fs_exec_hello_entry.spl` aborted with
5 files failing to compile. **Pre-existing:** the existing
`rebuild-sosix-qemu-media.shs` riscv64 row (`smoke_entry.spl`, same flags as
line 316) fails on the same `semihost.spl`, `syscall_shim.spl`,
`userlib/fs.spl` and `rv64_auth_trust_config` errors (measured with the same
seed, 2026-11-19). The fifth (`rv64_auth_trust_config` import) is a compiler
gap tracked separately in
`seed_single_segment_import_ignores_source_roots_2026-11-19.md`.

| file | error | cause | fix |
|---|---|---|---|
| `src/os/kernel/abi/syscall_shim.spl` | `llvm global load referenced undeclared symbol spl_handle_debug_write` (Cranelift: NULL function value) | a local `extern fn spl_handle_debug_write` shadowed the definition imported from `syscall_shim_process`; every other keepalive handler resolves through that import | delete the local extern |
| `src/os/kernel/boot/boot_fs_mount.spl` | `undeclared symbol NVFS_BOOT_ARENA_BASE_LBA_V1` | constant used without an import (the cross-module `pub val` itself resolves — probe: imported value is 4) | import it from `nvfs_root_mount_transaction` |
| `src/lib/nogc_async_mut_noalloc/baremetal/riscv/semihost.spl` | `cannot resolve method call Array.as_ptr` | riscv64 kernel arch files imported the `baremetal.riscv` package root, whose `__init__.spl` forwards `semihost`, `startup`, `plic`, ... so the closure compiled the M-mode semihost module into an S-mode SBI kernel | import the owning submodules (`.cmo`, `.sbi`) in `hal_cache`, `hal_smp`, `user_entry` |
| `src/os/userlib/fs.spl` | `cannot resolve method call str.parse_u8` | `text.parse_u8()` has no native lowering | decode the already-validated single ASCII digit (`byte_at(0) - 48`) |

`fd_io.spl` imports `os.userlib.fs` directly, so userlib/fs is a genuine kernel
dependency (not a closure leak). `src/os/tools/proc/nice_tool.spl:39` still
calls `parse_u8()`; it is outside kernel closures and is left as is.

## Regression specs

- `test/01_unit/os/kernel/abi/syscall_shim_keepalive_spec.spl`
- `test/01_unit/os/kernel/boot/boot_fs_mount_arena_import_spec.spl`
- `test/01_unit/os/kernel/arch/riscv64_kernel_closure_hygiene_spec.spl`

## Verification still owed

A clean riscv64 kernel native-build plus the OpenSBI boot rung
(`scripts/check/check-simpleos-riscv64-user-elf-opensbi.shs`).
