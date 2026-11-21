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

## Step 3a — restore definitions lost in e274cd33719 (verification-pending)

- `rv64_prepare_kernel_exit_context` + `RV64_KERNEL_RETURN_COOKIE`
  (`arch/riscv64/trap_model.spl`) and `vmm_copyin_packed_string_vector`
  (`memory/vmm_copy.spl`) were deleted by the stale-snapshot merge
  `e274cd33719` while their callers and imports survived. Restored verbatim
  from `e274cd33719^1`. The cookie matches the literal `_rv64_enter_user`
  still stores (`trap_vector.spl`). The `err` global is the `.err()` call on
  this function's result and should resolve with it.
- Spec: `test/01_unit/os/kernel/arch/riscv64_kernel_exit_context_spec.spl`
  (4/4 red before, 4/4 green after).
- Link unverified: WSL is down (virtual disk under repair), so the riscv64
  kernel was not relinked for this change.

## Step 3b — keepalive providers imported by name (verification-pending)

- With the LLVM 23 seed on ubuntu-p2, release/1.0.0 no longer reached the
  link: `syscall_shim.spl` failed with `llvm global load referenced undeclared
  symbol spl_shim_file_capability_check`. The symbol-form import workaround
  (0921af461ac, bug `compiled_hir_module_form_use_bare_names_2026-11-19`)
  missed 7 address-taken `_shim_keepalive` names (file/net capability checks,
  `spl_shim_current_task_id`). Added by-name imports.
- Spec: `syscall_shim_keepalive_spec.spl` now requires every keepalive name to
  be imported by name or defined locally (red: 8 missing; green after).

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

## Step 4a — `_rv64_enter_user` export + console import gating (2026-11-20, verification-pending)

- `trap_vector.spl`: the naked `_rv64_enter_user` trampoline now carries
  `@export("C", name: "_rv64_enter_user")` and returns `i64`, matching the
  `extern fn` in `user_entry.spl`/`context.spl`. Before this it was emitted only
  under its mangled module name (`llvm-nm`: `src__os__kernel__arch__riscv64__trap_vector___rv64_enter_user`).
  Kernel link on ubuntu-p2 (seed `~/zafix-target`): undefined 38 -> 37, and `_rv64_enter_user` is gone.
- `arch_adapt/console_byte.spl`: per-arch `use` lines are `@cfg`-gated. `rt_port_inb/outb`
  are still undefined, because another importer still pulls `x86/port_io_owner` into the
  riscv64 closure. That importer is the next step.
- Still open: `spl_handle_server_startup_evidence_consume_v1` (LLVM emits the
  definition as `.2`/`_dot_1` and the keepalive reference stays undefined; moving the definition
  above the keepalive did not change it) and `spl_thread_current_id` (`thread_shim` is not in the
  closure).
- Specs: `test/01_unit/os/kernel/arch/riscv64_enter_user_link_contract_spec.spl`,
  `hal_arch_gating_contract_spec.spl` ("cfg-gates every per-arch console import").

## Step 4b: compiler-rt builtins and S-mode primitives (2026-11-21, verification-pending)

- Seed: `rv64_kernel_primitives` is now in the `SIMPLE_BOOT_MINIMAL` allowlist, and
  `SIMPLE_COMPILER_RT_BUILTINS` names an explicit clang-built builtins archive. libgcc is rejected.
  LLVM 23's clang resource dir ships no riscv64 bare-metal builtins.
- Gate: `scripts/check/check-simpleos-riscv64-user-elf-opensbi.shs --link-only`. This is a minimal
  rebuild after the lane worktree was lost; the QEMU boot stage will be a separate change.
- Kernel link on ubuntu-p2: undefined 33 -> 23. `__fixdfdi`, `__nedf2`, `rt_memcpy`, `rt_memset`,
  `rt_load/store_barrier`, `rt_riscv64_{fence_i,sbi_call,syscall}`, and `unsafe_addr_of` are gone.
- Remaining 23: `memset`, `spl_thread_current_id`, and 21 `rt_*` helpers, most of which are defined only in
  hosted `src/runtime/runtime_native.c` or in `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`
  (that file is not compiled by the examples boot dir).
