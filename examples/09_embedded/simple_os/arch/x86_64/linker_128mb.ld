/*
 * x86_64 Bare-Metal Linker Script — 128 MiB base (GRUB-EFI / OVMF)
 *
 * Target: x86_64 processors booted via UEFI firmware (OVMF) -> GRUB-EFI ->
 *         multiboot1. This is the real-board boot chain (NOT QEMU `-kernel`).
 * Bootloader: Multiboot1 compatible.
 *
 * Why 128 MiB (0x08000000) instead of 1 MiB:
 *   The large merged ring-3 kernel occupies the whole low region [1MB, ~229MB]
 *   at a 1MB base (its file image + ~211MB NOBITS .bss). That starves GRUB-EFI's
 *   multiboot1 relocator of a safe low scratch/trampoline slot and faults
 *   (#UD at RIP~0x1012 in the relocator, caught by OVMF, before _start runs).
 *   Loading at 128MB leaves [1MB,128MB) free for GRUB's relocator + multiboot
 *   info while staying within the crt0 identity map (first 4GiB) and below the
 *   PMM heap (0x80000000). Kernel .bss then reaches ~0x16400000 (~356MB); the
 *   ring-3 payload is linked at 0x40000000 (1GiB, see sysroot.shs simpleos.ld)
 *   and the mmap base at 0x50000000, both clear of that band.
 *
 * Memory Layout:
 *   0x08000000 - Kernel load address (128MB mark)
 *   Identity-mapped first 4GB via page tables
 *
 * Sections:
 *   .text.entry - Multiboot1 header + _start (must be in first 8KB)
 *   .text       - Code and read-only data
 *   .rodata     - Read-only data (GDT, etc.)
 *   .data       - Initialized data
 *   .bss        - Uninitialized data (page tables, stack)
 *   .heap       - Dynamic memory allocation
 */

ENTRY(_entry32)

SECTIONS
{
    /* Kernel base 128MB — leaves [1MB,128MB) free for GRUB-EFI's multiboot1
     * relocator trampoline + boot info (see header). QEMU `-kernel` honours
     * p_paddr identically, but this variant is intended for the OVMF/GRUB-EFI
     * lane; the QEMU `-kernel` getfile lane keeps linker_low1mb.ld at 1MB. */
    . = 0x8000000;
    _kernel_start = .;

    /* Code section — .text.entry first for Multiboot header */
    .text ALIGN(4K) :
    {
        KEEP(*(.text.entry))
        KEEP(*(.multiboot))
        *(.text)
        *(.text.*)
    }
    /* The x86_64 boot crt0 places a fixed 28-byte Multiboot1 header at the
     * start of .text.entry, followed immediately by the 32-bit boot entry.
     * Some current toolchain paths are dropping the assembler's _entry32
     * symbol from the final ELF symbol table, which leaves e_entry as 0 and
     * makes QEMU reject the kernel image. Recreate the symbol at link time so
     * ENTRY(_entry32) always resolves to the actual boot code. */
    _entry32 = ADDR(.text) + 28;
    _start = _entry32;

    /* Read-only data */
    .rodata ALIGN(4K) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    /* Initialized data */
    .data ALIGN(4K) :
    {
        *(.data)
        *(.data.*)
    }

    /* Uninitialized data */
    .bss ALIGN(4K) :
    {
        __bss_start = .;
        *(COMMON)
        *(.bss)
        *(.bss.*)
        __bss_end = .;
    }

    /* Heap (grows upward) — NOLOAD so ld emits SHT_NOBITS and QEMU's
     * multiboot loader does not have to read/write megabytes of zero
     * content out of the ELF file. */
    .heap ALIGN(4K) (NOLOAD) :
    {
        __heap_start = .;
        . = . + 16M;  /* 16MB linker-script heap (in addition to _heap[]) */
        __heap_end = .;
    }

    /* Stack (grows downward) — NOLOAD for the same reason. Without this
     * ld marks the section PROGBITS, inflates the ELF file by the stack
     * size, and QEMU either truncates the kernel load or extends the
     * kernel image beyond the configured -m memory. The resulting
     * stack-pointer-above-physical-RAM was the root cause of Agent M's
     * 0x950a cascading fault. */
    .stack ALIGN(4K) (NOLOAD) :
    {
        . = . + 8M;  /* 8MB stack — Simple code uses large stack frames */
        _stack_top = .;
    }

    /* End of kernel */
    _kernel_end = .;

    /*
     * Strong C-ABI aliases for spl_handle_* syscall shims.
     *
     * The Simple compiler's --entry-closure DCE retains the functions (visible
     * as kernel__abi__syscall_shim__spl_handle_* W symbols) but does NOT emit
     * strong --defsym aliases for @export("C") on non-entry functions.
     * The weak stubs in baremetal_stubs.c therefore win the W vs W arbitration.
     *
     * These linker-script assignments create strong (T) aliases that override
     * both the weak baremetal stubs and the internal mangled names.
     *
     * One entry per spl_handle_* function defined in
     * src/os/kernel/abi/syscall_shim.spl (62 shims, Wave 10D).
     */
    /* Syscall-shim aliases.
     *
     * GENERATED, not hand-maintained.  The previous hand-written block assumed
     * every shim lived in one module and mangled as
     * `kernel__abi__syscall_shim__spl_handle_*`.  That layout no longer exists:
     * the shims were split into syscall_shim_{process,ipc,file,net,device,...}
     * and the seed emits a `src__os__` prefix, so all 66 assignments named
     * symbols that are defined nowhere and ld.lld failed the link outright.
     * Same staleness class as the B1 facade re-exports, in the linker script.
     *
     * PROVIDE() rather than `=`: a plain assignment to a missing symbol is a
     * hard error even when nothing references the alias, which made the script
     * brittle against --entry-closure pruning.  PROVIDE is evaluated only when
     * the alias is actually referenced and still undefined.
     *
     * Mangled names below were derived from the kernel objects built by the
     * Rust seed at 91b6b9f28dd; regenerate if the mangling scheme changes.
     * Note this script is shared with the SSH lane, which carried the same
     * latent link failure.
     */
    PROVIDE(spl_handle_alloc_dma = src__os__kernel__abi__syscall_shim_device__spl_handle_alloc_dma);
    PROVIDE(spl_handle_brk = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_brk);
    PROVIDE(spl_handle_cap_grant = src__os__kernel__abi__syscall_shim_file__spl_handle_cap_grant);
    PROVIDE(spl_handle_chdir = src__os__kernel__abi__syscall_shim_file__spl_handle_chdir);
    PROVIDE(spl_handle_clock_gettime = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_clock_gettime);
    PROVIDE(spl_handle_debug_write = src__os__kernel__abi__syscall_shim_process__spl_handle_debug_write);
    PROVIDE(spl_handle_dev_enumerate = src__os__kernel__abi__syscall_shim_device__spl_handle_dev_enumerate);
    PROVIDE(spl_handle_dev_get_info = src__os__kernel__abi__syscall_shim_device__spl_handle_dev_get_info);
    PROVIDE(spl_handle_device_grant = src__os__kernel__abi__syscall_shim_device__spl_handle_device_grant);
    PROVIDE(spl_handle_dup = src__os__kernel__abi__syscall_shim_file__spl_handle_dup);
    PROVIDE(spl_handle_dup2 = src__os__kernel__abi__syscall_shim_file__spl_handle_dup2);
    PROVIDE(spl_handle_enter_user_blocking = src__os__kernel__abi__syscall_shim_process__spl_handle_enter_user_blocking);
    PROVIDE(spl_handle_exec = src__os__kernel__abi__syscall_shim_file__spl_handle_exec);
    PROVIDE(spl_handle_exit = src__os__kernel__abi__syscall_shim_process__spl_handle_exit);
    PROVIDE(spl_handle_fcntl = src__os__kernel__abi__syscall_shim_file__spl_handle_fcntl);
    PROVIDE(spl_handle_file_close = src__os__kernel__abi__syscall_shim_file__spl_handle_file_close);
    PROVIDE(spl_handle_file_mkdir = src__os__kernel__abi__syscall_shim_file__spl_handle_file_mkdir);
    PROVIDE(spl_handle_file_open = src__os__kernel__abi__syscall_shim_file__spl_handle_file_open);
    PROVIDE(spl_handle_file_read = src__os__kernel__abi__syscall_shim_file__spl_handle_file_read);
    PROVIDE(spl_handle_file_readdir = src__os__kernel__abi__syscall_shim_file__spl_handle_file_readdir);
    PROVIDE(spl_handle_file_stat = src__os__kernel__abi__syscall_shim_file__spl_handle_file_stat);
    PROVIDE(spl_handle_file_sync = src__os__kernel__abi__syscall_shim_file__spl_handle_file_sync);
    PROVIDE(spl_handle_file_write = src__os__kernel__abi__syscall_shim_file__spl_handle_file_write);
    PROVIDE(spl_handle_fork = src__os__kernel__abi__syscall_shim_file__spl_handle_fork);
    PROVIDE(spl_handle_free_dma = src__os__kernel__abi__syscall_shim_device__spl_handle_free_dma);
    PROVIDE(spl_handle_fs_pread_registered_v1 = src__os__kernel__abi__syscall_shim_positioned__spl_handle_fs_pread_registered_v1);
    PROVIDE(spl_handle_fs_pwrite_registered_v1 = src__os__kernel__abi__syscall_shim_positioned__spl_handle_fs_pwrite_registered_v1);
    PROVIDE(spl_handle_ftruncate = src__os__kernel__abi__syscall_shim_file__spl_handle_ftruncate);
    PROVIDE(spl_handle_getcwd = src__os__kernel__abi__syscall_shim_file__spl_handle_getcwd);
    PROVIDE(spl_handle_get_hostname = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_get_hostname);
    PROVIDE(spl_handle_get_parent_pid = src__os__kernel__abi__syscall_shim_process__spl_handle_get_parent_pid);
    PROVIDE(spl_handle_getpid = src__os__kernel__abi__syscall_shim_process__spl_handle_getpid);
    PROVIDE(spl_handle_get_task_info = src__os__kernel__abi__syscall_shim_process__spl_handle_get_task_info);
    PROVIDE(spl_handle_ipc_connect = src__os__kernel__abi__syscall_shim_ipc__spl_handle_ipc_connect);
    PROVIDE(spl_handle_ipc_create_port = src__os__kernel__abi__syscall_shim_ipc__spl_handle_ipc_create_port);
    PROVIDE(spl_handle_ipc_recv = src__os__kernel__abi__syscall_shim_ipc__spl_handle_ipc_recv);
    PROVIDE(spl_handle_ipc_send = src__os__kernel__abi__syscall_shim_ipc__spl_handle_ipc_send);
    PROVIDE(spl_handle_list_tasks = src__os__kernel__abi__syscall_shim_process__spl_handle_list_tasks);
    PROVIDE(spl_handle_log_read = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_log_read);
    PROVIDE(spl_handle_log_write = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_log_write);
    PROVIDE(spl_handle_lseek = src__os__kernel__abi__syscall_shim_file__spl_handle_lseek);
    PROVIDE(spl_handle_map_bar = src__os__kernel__abi__syscall_shim_device__spl_handle_map_bar);
    PROVIDE(spl_handle_mem_grant = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_mem_grant);
    PROVIDE(spl_handle_mem_revoke = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_mem_revoke);
    PROVIDE(spl_handle_mmap = src__os__kernel__abi__syscall_shim_process__spl_handle_mmap);
    PROVIDE(spl_handle_mount = src__os__kernel__abi__syscall_shim_file__spl_handle_mount);
    PROVIDE(spl_handle_mprotect = src__os__kernel__abi__syscall_shim_process__spl_handle_mprotect);
    PROVIDE(spl_handle_munmap = src__os__kernel__abi__syscall_shim_process__spl_handle_munmap);
    PROVIDE(spl_handle_net_accept = src__os__kernel__abi__syscall_shim_net__spl_handle_net_accept);
    PROVIDE(spl_handle_net_bind = src__os__kernel__abi__syscall_shim_net__spl_handle_net_bind);
    PROVIDE(spl_handle_net_connect = src__os__kernel__abi__syscall_shim_net__spl_handle_net_connect);
    PROVIDE(spl_handle_net_if_config = src__os__kernel__abi__syscall_shim_net__spl_handle_net_if_config);
    PROVIDE(spl_handle_net_listen = src__os__kernel__abi__syscall_shim_net__spl_handle_net_listen);
    PROVIDE(spl_handle_net_recv_from = src__os__kernel__abi__syscall_shim_net__spl_handle_net_recv_from);
    PROVIDE(spl_handle_net_send_to = src__os__kernel__abi__syscall_shim_net__spl_handle_net_send_to);
    PROVIDE(spl_handle_net_socket = src__os__kernel__abi__syscall_shim_net__spl_handle_net_socket);
    PROVIDE(spl_handle_notification_create = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_create);
    PROVIDE(spl_handle_notification_destroy = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_destroy);
    PROVIDE(spl_handle_notification_poll = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_poll);
    PROVIDE(spl_handle_notification_signal = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_signal);
    PROVIDE(spl_handle_notification_wait = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_wait);
    PROVIDE(spl_handle_notification_wait_any = src__os__kernel__abi__syscall_shim_ipc__spl_handle_notification_wait_any);
    PROVIDE(spl_handle_pipe = src__os__kernel__abi__syscall_shim_file__spl_handle_pipe);
    PROVIDE(spl_handle_pledge = src__os__kernel__abi__syscall_shim_file__spl_handle_pledge);
    PROVIDE(spl_handle_poll = src__os__kernel__abi__syscall_shim_file__spl_handle_poll);
    PROVIDE(spl_handle_privctl = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_privctl);
    PROVIDE(spl_handle_rename = src__os__kernel__abi__syscall_shim_file__spl_handle_rename);
    PROVIDE(spl_handle_rmdir = src__os__kernel__abi__syscall_shim_file__spl_handle_rmdir);
    PROVIDE(spl_handle_safecopy_from = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_safecopy_from);
    PROVIDE(spl_handle_safecopy_to = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_safecopy_to);
    PROVIDE(spl_handle_schedctl = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_schedctl);
    PROVIDE(spl_handle_schedule = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_schedule);
    PROVIDE(spl_handle_set_hostname = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_set_hostname);
    PROVIDE(spl_handle_set_priority = src__os__kernel__abi__syscall_shim_process__spl_handle_set_priority);
    PROVIDE(spl_handle_signal = src__os__kernel__abi__syscall_shim_process__spl_handle_signal);
    PROVIDE(spl_handle_sleep = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_sleep);
    PROVIDE(spl_handle_spawn = src__os__kernel__abi__syscall_shim_process__spl_handle_spawn);
    PROVIDE(spl_handle_spawn_binary = src__os__kernel__abi__syscall_shim_process__spl_handle_spawn_binary);
    PROVIDE(spl_handle_sysinfo = src__os__kernel__abi__syscall_shim_time_log_sysinfo__spl_handle_sysinfo);
    PROVIDE(spl_handle_sys_mmap = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_sys_mmap);
    PROVIDE(spl_handle_sys_munmap = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_sys_munmap);
    PROVIDE(spl_handle_system_reboot = src__os__kernel__abi__syscall_shim_g11g12g13__spl_handle_system_reboot);
    PROVIDE(spl_handle_unlink = src__os__kernel__abi__syscall_shim_file__spl_handle_unlink);
    PROVIDE(spl_handle_unmount = src__os__kernel__abi__syscall_shim_file__spl_handle_unmount);
    PROVIDE(spl_handle_unveil = src__os__kernel__abi__syscall_shim_file__spl_handle_unveil);
    PROVIDE(spl_handle_wait = src__os__kernel__abi__syscall_shim_process__spl_handle_wait);
    PROVIDE(spl_handle_waitpid = src__os__kernel__abi__syscall_shim_file__spl_handle_waitpid);
    PROVIDE(spl_handle_yield = src__os__kernel__abi__syscall_shim_process__spl_handle_yield);

    /* Debug sections */
    .debug_info 0 : { *(.debug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev) }
    .debug_line 0 : { *(.debug_line) }
    .debug_str 0 : { *(.debug_str) }
    .debug_frame 0 : { *(.debug_frame) }
    .debug_loc 0 : { *(.debug_loc) }
    .debug_ranges 0 : { *(.debug_ranges) }

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
