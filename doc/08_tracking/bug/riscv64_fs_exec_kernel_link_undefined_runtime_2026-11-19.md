# riscv64 fs-exec kernel: link fails with undefined runtime/arch symbols

- **Status:** verification-pending (batch 1 landed; remaining batches tracked below)
- **Found:** 2026-11-19, `scripts/check/check-simpleos-riscv64-user-elf-opensbi.shs`
  (entry `examples/09_embedded/simple_os/arch/riscv64/fs_exec_hello_entry.spl`)
- **Symptom:** kernel compiles (606 objects) but `ld.lld` reports 47 undefined symbols.

## Cause

The native linker compiles boot C from exactly one `boot/` dir (the entry's).
`examples/.../riscv64/boot` carries the core value/string runtime and the
virtio-blk driver (`arch/common/riscv_common.h`); `src/os/kernel/arch/riscv64/boot`
carries the S-mode primitives. Neither alone satisfies the kernel closure.
Moving the entry into the kernel tree made it worse (71 undefined).

## Batch 1 (this change) — 47 -> 36, 0 duplicates

- S-mode primitives (`rt_riscv64_syscall`, `rt_riscv64_fence_i`,
  `rt_riscv64_sbi_call`, `rt_memcpy`, `rt_memset`, `rt_load_barrier`,
  `rt_store_barrier`, `unsafe_addr_of`) moved verbatim into
  `src/os/kernel/arch/riscv64/boot/rv64_cpu_primitives.inc.h`, included by the
  kernel `freestanding_runtime.c` and by the new examples TU
  `examples/.../riscv64/boot/rv64_kernel_primitives.c` (single source).
- `rt_riscv64_virtio_blk_fat32_{init,capacity_sectors,read_sector_bytes}`:
  thin wrappers in examples `baremetal_stubs.c` over the existing
  `riscv_common.h` virtio-blk driver (no second driver instance).

Evidence: replaying the seed's `freestanding_link.rsp` with the recompiled
objects (seed flags `-ffunction-sections -fdata-sections -fno-pie`) drops the
undefined set from 47 to 36 with no duplicate definitions.

## Batch 2 — arch HAL routing (verification-pending)

- `src/os/kernel/arch_adapt/console_byte.spl` (new): `hal_console_{read,write}_byte`
  with one `@cfg` body per target; `sosix/io_rw.spl` calls it instead of
  `x86_com1_*`.
- `drivers/pci/pci.spl`: port-I/O config access is `@cfg(x86_64)`/`@cfg(x86)`
  only; arm64/riscv64 read and write via ECAM (all-ones / dropped while no ECAM
  base is wired).
- `kernel/memory/vmm.spl`: `_invlpg` is per-arch; riscv64 uses
  `sfence_vma_addr`, riscv32 `sfence_vma`; x86/arm keep `rt_invlpg`.
- Contract spec: `test/01_unit/os/kernel/arch_adapt/hal_arch_gating_contract_spec.spl`
  (4/4 red on the base, 4/4 green with the change).
- Link-count delta not yet measured: the WSL distro failed to start
  (`Wsl/Service/CreateInstance/E_FAIL`, code 5) when this landed.

## Remaining (36 before batch 2)

- x86 port I/O live via `sosix/io_rw.spl` -> `x86_com1_read_byte`; `rt_invlpg`
  via `kernel/memory/vmm.spl`. Route through the arch HAL. (Batch 2.)
- Core runtime helpers absent from the examples runtime: typed words/bytes,
  `rt_array_{fill_span,is_byte_packed,get_text,set_text,repeat,new_with_cap_u64}`,
  `rt_text_{find,is_ascii}`, `rt_slice_text_bytes`, `rt_string_{char_count,from_byte_array}`,
  `rt_numeric_contains_u64`, `rt_any_to_int`, `rt_atomic_int_store`,
  `rt_mutex_{lock,unlock}`, `rt_stdout_write`, `rt_copy_user_byte`, `memset`,
  soft-float `__fixdfdi`/`__nedf2`.
- Unresolved names lowered to globals: `rv64_prepare_kernel_exit_context`,
  `err` (`riscv64/interrupt.spl`), `vmm_copyin_packed_string_vector`
  (`ipc/syscall_process.spl`); `_rv64_enter_user`; `spl_thread_current_id`;
  `spl_handle_server_startup_evidence_consume_v1`.
