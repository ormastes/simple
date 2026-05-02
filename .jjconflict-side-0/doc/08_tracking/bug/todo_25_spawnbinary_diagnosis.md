# TODO #25 Diagnosis — x86_64 SpawnBinary Bridge Fault

**Date:** 2026-04-15  
**TODO ref:** `doc/TODO.md:75-78`, `baremetal_stubs.c:3462` (case 13 in `userlib__syscall_raw__syscall`)

---

## Exact Failure Point

`src/os/kernel/ipc/syscall.spl` — `dispatch_spawn_binary_direct` (line 609), specifically
the `sched.create_user_task(image_result.unwrap(), priority, caps)` call (line 661).

The bootstrap Scheduler installed via `X86TrapRuntime.bootstrap(64)` is a minimal
log-only singleton — it has no real process table, no page-table management, and no
context-switch support. Calling `create_user_task` on it to actually place a real user
task image triggers a fault (null deref or stack smash) before the task launches.

The section header at `baremetal_stubs.c:3438` ("8b. Bare-metal syscall stub") is a
comment, not the TODO itself. The live SpawnBinary path is the `case 13` block at line
3462.

---

## Call Chain (x64-desktop-disk lane)

```
src/os/userlib/process.spl spawn_binary(path, priority)
  -> userlib__syscall_raw__syscall(13, path_ptr, path_len, priority_raw, 0, 0)
     [baremetal_stubs.c:3462]
  -> kernel__arch__x86_64__interrupt__x86_dispatch_installed_syscall_abi(13, ...)
     [src/os/kernel/arch/x86_64/interrupt.spl:226 — if runtime installed]
  -> dispatch_spawn_binary_direct(arg0, arg1, arg2, runtime.scheduler, runtime.klog)
     [src/os/kernel/ipc/syscall.spl:609]
  -> _copy_user_text(path_ptr, path_len)          # succeeds
  -> resolve_executable_bytes(path, arch)          # succeeds (or falls to disk/builtin)
  -> build_user_process_image(...)                 # succeeds
  -> sched.create_user_task(image, priority, caps) # FAULTS — bootstrap Scheduler stub
```

Note: `desktop_e2e_entry.spl` itself does NOT hit this path. Its launcher shortcut uses
`materialize_resident_launch` (manifest-based fake-spawn) and never calls syscall 13
directly. The fault only fires on the `x64-desktop-disk` scenario where `spawn_binary`
is called from user-level launcher code.

---

## Proposed Fix (3 steps)

1. **Make bootstrap Scheduler safe on baremetal.** In
   `src/os/kernel/scheduler/scheduler.spl`, make `create_task` / `create_user_task`
   return a stub `TaskId(id: 1)` and log a warning when called on a bootstrap-mode
   Scheduler that has no real process infrastructure. This prevents the fault and lets
   the caller handle the non-zero return as "launched" without a real context switch.

2. **Expand the 3-entry GDT to 5 entries** (`examples/simple_os/arch/x86_64/boot/crt0.s`).
   The current null/kernel-CS/kernel-DS layout prevents MSR_STAR programming; adding
   user-CS32, user-DS, user-CS64 descriptors is the prerequisite for enabling
   SYSCALL/SYSRET so user tasks can return to ring 0 (cpu.spl:122-136 blocker).

3. **Wire `spl_handle_spawn_binary` through `shim_init`.** The strong C-exported symbol
   `spl_handle_spawn_binary` (syscall_shim.spl:456) is already linked when
   `desktop_e2e_entry.spl` pulls in `syscall_shim`. Verify that `shim_init` stores the
   Scheduler instance constructed in `desktop_e2e_main` (not the bootstrap-minimal one)
   so `x86_dispatch_installed_syscall_abi` sees a scheduler capable of real task
   creation when step 1 is complete.

---

## SFFI Recommendation

Plain FFI is correct: the C-to-Simple boundary (`kernel__arch__x86_64__interrupt__x86_dispatch_installed_syscall_abi`) passes only primitive types (u64/i64); composite types (Scheduler, KernelLog) flow entirely within Simple across the call chain, never crossing the FFI boundary. `sffi_bi` is not needed.

---

## Scope Audit

Files read (not modified): `baremetal_stubs.c`, `interrupt.spl`, `syscall.spl`,
`cpu.spl`, `desktop_e2e_entry.spl`, `process.spl`, `syscall_shim.spl`, `TODO.md`.  
File written: `doc/08_tracking/bug/todo_25_spawnbinary_diagnosis.md` (this file).  
No files outside the allowlist were modified.
