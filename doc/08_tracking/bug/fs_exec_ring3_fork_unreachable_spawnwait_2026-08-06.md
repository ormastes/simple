# Lane B3 — fork() is UNREACHABLE on the ring-3 FS-exec path; SpawnWait(120) landed, in-guest proof BLOCKED

Date: 2026-08-06
Lane: B3 of `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## 1. Mechanism — fork is unreachable, not broken

The plan and `in_guest_clang_selfhost_board_plan.md` say fork is "absent on the
ring-3 FS-exec clang path". The precise reason, with evidence:

**Fork(57)/Exec(59) ARE fully implemented and ARE wired.**
- `src/os/kernel/ipc/syscall_process.spl:237` `_handle_fork` — calls
  `sched.get_current()` then `sched.clone_task(parent)`.
- `src/os/kernel/ipc/syscall_process.spl:252` `_handle_exec` — builds a
  `UserProcessImage` and calls `sched.exec_image(current, ...)`.
- `src/os/kernel/abi/syscall_shim_file.spl:415` / `:426` export them as the
  strong C symbols `spl_handle_fork` / `spl_handle_exec`.
- `baremetal_stubs.c:17202` / `:17203` dispatch syscalls 57/59 to those symbols.

**They are unreachable from an FS-exec ring-3 process for two independent reasons.**

*(a) The process is not a scheduler Task, so there is nothing to clone.*
`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:311` `_x86_64_fs_exec_enter_ring3`
hand-builds an address space (`create_user_address_space` +
`vmm_clone_kernel_low_private` + `_map_pt_loads` + a hand-built SysV stack
frame) and `iretq`s to CPL3 via `arch_x86_64_enter_user_task` (`:437`). It never
calls `create_task`, never mints a `TaskId`, and never calls
`register_task_vmspace`. The kernel then BLOCKS inside that call frame until the
program's `exit(2)` longjmps back (`:449`).
**No address-space copy ever fails, because none is ever attempted** —
`sched.get_current()` has no user task to return and `clone_task` has no process
image to duplicate. Same for `exec_image`.

*(b) The bare-exec dispatcher intercepts before the shim and has no 57/59/61.*
`rt_user_heap_init` (`baremetal_stubs.c:16569`), which the heap ring-3 entry
always calls, sets `_bare_exec_mode = 1`. `rt_syscall_dispatch:17126` then offers
every syscall to `_bare_exec_handle` (`:16712`) FIRST. That switch handles
0, 4, 10, 11, 12, 15, 30–34, 39, 43, 44, 46, 47, 50, 60, 69 — and **no 57, no 59,
no 61 (waitpid)**.

**Three further structural blockers**, any one of which alone defeats a naive fork:
- **Single-slot savepoint.** `enter_user_first.s` had ONE global
  `_ring3_resume_buf` + `_ring3_resume_valid`, consumed on use (`:121`). A nested
  entry destroys the parent's resume point.
- **Halt-on-exit.** `rt_user_heap_init` also set `_bare_exec_halt_on_exit = 1`,
  and `_bare_exec_handle` case 0 takes `outb(0xF4)` (QEMU isa-debug-exit) rather
  than resuming. A child's exit would take the machine down, not return a status.
- **Shared RAM file table.** `rt_user_heap_init` calls `_bare_exec_reset_files()`,
  and `x86_64_fs_exec_spawn_heap` calls `simpleos_bare_exec_reset()` — a child
  would wipe the parent's fds and the only place a `.o` can live.

**Prior half-landed attempt (finding).** `rt_user_heap_init_returning`
(`baremetal_stubs.c:16578`) already existed with `_bare_exec_halt_on_exit = 0`
and **zero callers anywhere in the tree** — and
`test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl:22` actively asserts
the spawn path does NOT use it. Someone started this lane and stopped.

## 2. What was implemented — SpawnWait, syscall 120

Full copy-on-write fork is a scheduler-integration project (make FS-exec
processes real Tasks with registered vmspaces). The smaller sufficient primitive
was built instead: **posix_spawn + waitpid fused into one synchronous call**,
which is exactly what a compiler driver needs.

- `enter_user_first.s` — savepoint is now a **stack** (`_ring3_resume_depth` +
  `RING3_RESUME_MAX_DEPTH = 4` slots); push on entry, pop on resume. The
  `rt_x86_ring3_resume_valid` accessor returns the depth, so every existing
  `!= 0` caller is unchanged. **cr3 is argued to need no new code**: the
  savepoint captures whatever AS the kernel is running under, which is the
  kernel PML4 for a top-level spawn and the PARENT's AS for a nested one, so
  restoring it should land the parent back in its own address space by
  construction. **This is reasoning, never executed** — D6 blocks reaching a
  nested spawn at all. It is the subtlest part of the design and the most likely
  place a nested spawn actually dies; treat it as unverified.
- `baremetal_stubs.c` — `rt_bare_spawn_enter/leave/depth` save and restore
  `_user_heap_{base,cur,end}` and `_bare_exec_halt_on_exit`; while nested,
  `rt_user_heap_init` forces halt-off and skips the file reset,
  `simpleos_bare_exec_reset()` is a no-op, and `_bare_dump_all_outputs()` runs
  only at depth 0. Syscall **120** dispatches to `spl_handle_spawn_wait`
  (+ weak ENOSYS stub). **Not 57/59** — they mean scheduler fork in the full
  kernel. **Not 70** — that is already `net_socket` (`:17296`); a first draft used
  70 and produced a duplicate `case` label in the same switch.
- `src/os/kernel/loader/x86_64_fs_exec_spawn.spl` — `x86_64_fs_exec_spawn_wait()`
  and the `@export("C") spl_handle_spawn_wait` handler. ABI: `a0`=path ptr,
  `a1`=path len, `a2`=argv blob (NUL-separated), `a3`=blob len, `a4`=argc.
  A packed blob, not a `char**` table, so copy-in is a single byte loop.
  Carries the `ponytail:` ceiling note.

**Ceiling** (documented at both sites): synchronous run-to-completion; parent
fully suspended; no concurrency, so no pipes and no signals; child's exit status
(plus the shared RAM file table) is the only channel; nesting capped at 4; each
level leaks an 8 MiB stack + 64 MiB heap until reboot.
**Upgrade path**: give FS-exec processes real Tasks + `register_task_vmspace`
entries; `_handle_fork`/`_handle_waitpid` then become reachable **unchanged** and
this whole layer is deleted.

## 3. Proof status — blocked, and NOT reported as green

- **OVMF real-firmware baseline PASSES.** `sh scripts/os/ssh_ring3_uefi_boot.shs`
  reaches "PRIMARY GATE PASS: sshd accept loop started under OVMF". Its
  ssh-exec bonus MISSED — the guest sits in `[tcp-accept] EAGAIN` and never
  accepts the connection (virtio-net stall on this host). That is why the proof
  was built as a boot-time entry rather than an ssh command.
- `scripts/os/build_spawn_wait_ring3.shs` — fail-closed OVMF-pflash probe (never
  `-kernel`). Payload `examples/09_embedded/simpleos_hello_c/spawn_wait_fs.c` is
  ONE ELF that is both parent and child, selected by argv — the same shape as
  `clang` re-invoking itself as `clang -cc1`.
  Entry `examples/09_embedded/simple_os/arch/x86_64/fs_exec_spawn_wait_ring3_entry.spl`.
- Ladder reached today: GRUB EFI **ok**, multiboot -> `_start` **ok**, NVMe +
  FAT32 mount + `/FSEXEC.ELF` open (`file_size=14024`) **ok**, pmm+vmm **ok**.
  Ring-3 entry **BLOCKED** by D5.

### D5 — RESOLVED (it was my own asm bug, and the build system HID it)

`nm build/os/spawn_wait_ring3.elf` showed `rt_x86_enter_user_first` /
`rt_x86_ring3_resume` as **W (weak)** with `_ring3_resume_buf` /
`_ring3_resume_depth` **absent**, and the build log said
`FABRICATED-NEW spawn_wait_ring3.elf rt_x86_enter_user_first`.

Root cause: the first version of the savepoint-stack edit inserted prose into
`enter_user_first.s` **after** the closing `*/` of the preceding comment, so the
file no longer assembled. **native-build did not fail** — under
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` it FABRICATED weak stubs for the missing
symbols and linked a kernel that could never reach CPL3. Verified by assembling
the file standalone (`clang --target=x86_64-unknown-elf -c`), which showed the
real errors.

**This is itself a filable defect**: a `.s` file that fails to assemble is
silently replaced by fabricated stubs, producing a green build and a kernel with
a no-op `iretq` path. The only thing that caught it was the probe script's
symbol guard.

After the fix, `enter_user_first.s` assembles clean with all symbols
(`_ring3_resume_buf` B, `_ring3_resume_depth` B, `rt_x86_enter_user_first` T,
`rt_x86_ring3_resume` T, `rt_x86_ring3_resume_depth` T), the B3 kernel passes
the symbol guard, and — **regression check** — the production sshd kernel
(`scripts/os/ssh_clang_hello_ring3.shs`) rebuilds cleanly with the same symbols
as **T/B**. No ring-3 lane is regressed by the savepoint-stack change.

### D6 (BLOCKING, pre-existing, NOT Lane B3) — `vmm_kernel_pml4_phys()` reads 0 in another module after a successful `vmm_init`

With the asm correct, the ladder now reaches the ring-3 handoff and fails there:

```
[VMM] Initializing virtual memory manager...
[VMM] PML4 at physical 0x402718720
[VMM] VMM initialization complete
[b3] pmm+vmm online
[VMM] create_user_address_space: VMM not initialized — legacy AS=1
[spawn] FAIL user-AS synthetic root=1
[b3] parent returned rc=-1
```

`create_user_address_space` (`src/os/kernel/memory/vmm_address_space.spl:75`)
gates on `vmm_kernel_pml4_phys()`, which returns the module var `_vmm_pml4_phys`
in `src/os/kernel/memory/vmm_core.spl:191`. VMM init clearly allocated a PML4
(it printed the physical address from inside its own module), but the read from
the caller's module yields 0 — a cross-module module-var write-visibility
failure under freestanding native-build, the same family as the documented
landmines. **Nothing in Lane B3's change touches this path**; it sits between
`vmm_init` and the ring-3 loader and blocks every FS-exec ring-3 lane on this
entry equally.

Consequence: the spawn+wait round trip is **UNPROVEN in-guest** and must not be
claimed. The probe fails closed (symbol guard + every ladder rung must appear),
so no false green is possible.

## 4. Incidental fixes made along the way

- `examples/09_embedded/simpleos_hello_c/make_fsexec_base_image.spl` (new) —
  regenerates the FAT32 base image `patch_fsexec_image.spl` needs. That base is
  gitignored and was absent, making the whole ring-3 FS-exec lane unrunnable
  from a clean tree.
- **`s[i] as u8` on `text` silently yields ZERO** under `bin/simple run`. It
  produced a structurally valid FAT32 volume that mounted fine (`BPS=0200 SPC=01
  reserved=20 FATs=02 root_cluster=02`) but whose OEM field and `FSEXEC.ELF`
  dirent name were all NULs, so the file could never be found. Use explicit byte
  codes. Worth a separate bug if not already filed.

## 5. Next steps

1. Fix **D6** (`vmm_kernel_pml4_phys()` reading 0 cross-module after a
   successful `vmm_init`), then re-run `sh scripts/os/build_spawn_wait_ring3.shs`
   — every other ladder rung already passes. This is a pre-existing kernel
   defect, so fixing it unblocks the other FS-exec ring-3 entries too.
2. File the fabricated-stub defect from D5 separately: a `.s` that fails to
   assemble should FAIL the build, not be silently replaced by weak stubs.
3. Once the probe is green, verify the cr3 restore claim in §2 empirically (it
   is currently reasoning only).
4. Then wire the clang driver to syscall 120 and run the plan's stated B3
   acceptance (`clang hello.c -o hello` in driver mode). That needs C1
   (`build/os/clang_static` is absent today), so it is a separate lane.
