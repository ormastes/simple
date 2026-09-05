# 22 kernel functions are `use`-imported but defined nowhere in the tree

**Filed** 2026-09-01 · **Status** OPEN (routed around, not fixed) · **Severity** high

## Symptom
These names are imported by real modules via `use`, are called, and have **no
definition anywhere** in `src/` or `examples/`. They surface only as undefined
symbols when a lane's `--entry-closure` happens to reach them:

    staged_process_entry, staged_process_file_bytes, staged_process_initial_sp,
    staged_process_initial_stack_bytes, staged_process_segment_align,
    staged_process_segment_count, staged_process_segment_data,
    staged_process_segment_file_size, staged_process_segment_flags,
    staged_process_segment_mem_size, staged_process_segment_virt_addr,
    staged_process_stack_size, staged_process_stack_top,
    stage_user_process_image_for_scheduler,
    sched_prepare_exit_task_by_id_impl,
    sched_finalize_exit_task_by_id_with_code_impl,
    vmm_copyin_packed_string_vector, vmm_munmap_result, vmm_shared_unmap,
    pci_bdf_bus, pci_bdf_device, pci_bdf_function,
    app_registry_cached_boot_app_id, app_registry_leaf_for_canonical,
    container_view_allows_path, riscv64_fs_exec_spawn_authenticated_capture_with_launch_v1,
    rv64_prepare_kernel_exit_context, sosix_fs_kernel_uninstalled_positioned_state_v1,
    nvfs_posix_pread_bytes_owned, _copy_owned_payload, _owned_receive_without_message

Example: `src/os/kernel/ipc/syscall.spl:35` imports `pci_bdf_bus` from
`os.kernel.types.device_mem_types`; that module exists and does **not** define it.
Same shape for `container_view_allows_path` (`container_namespace`) and
`rv64_prepare_kernel_exit_context` (`riscv64.trap_model`).

## How it was found
The riscv64 WM render-smoke entry imports only `display` and `console`. Its
closure nevertheless demanded all of the above, because `console.spl` -- imported
purely for `serial_init()` -- also hosts the interactive console shell and so
imports `fs_exec_spawn` and `vfs_write_ops`, pulling in the scheduler, VFS, IPC
syscall table, PCI, fat32 and the compression stack.

## Status
**Routed around, not fixed.** The WM entry now brings the UART up via
`console_common` directly, which cuts that import edge and removes these symbols
from its closure. The underlying debt is untouched: any lane whose closure
reaches the console shell, the scheduler exit path, or the IPC syscall table
still cannot link, and nothing detects the condition until link time.

## Fix sketch
Implement or delete each. A `use` of a name the target module does not export
should be a resolve-time error, not a link-time undefined symbol -- that check is
the real fix, since it makes the whole class visible at once instead of one
lane's closure at a time.
