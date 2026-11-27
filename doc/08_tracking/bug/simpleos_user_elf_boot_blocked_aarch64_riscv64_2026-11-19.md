# SimpleOS aarch64/riscv64 user ELFs: no boot lane, and internal-link layout divergences

- status: open
- found: 2026-11-19 (lane ssos)

## Boot blocker (not a linker defect)
No in-tree lane runs a filesystem-loaded user ELF on aarch64 or riscv64:
- `check-simpleos-aarch64-hello-world-in-guest-efi.shs` (AAVMF): program runs at EL1;
  no aarch64 EL0 map+enter path in the Limine lane.
- `check-simpleos-riscv64-hello-world-in-guest-opensbi.shs` (OpenSBI fw_payload):
  program runs in S-mode; `_rv64_enter_user` exists but needs the scheduler + ELF
  loader closure.
Both also need the Rust seed (`SIMPLE_BIN`), absent in this WSL host.
So the internally linked user ELFs from `link_simpleos_user_64` cannot be booted yet.

## llvm-readelf comparison, internal vs ld.lld (C hello + sysroot libsimpleos_all.a)
Same on both arches: ELF type EXEC, e_machine, e_entry (0x50000000 / 0x100000000),
e_flags (rv64 0x5 RVC|double), RX and R PT_LOADs (same size), .text/.rodata sizes.
Divergences:
1. Synthesized `.got` (orphan) is placed after `.bss`; lld places it after `.data`.
   Effect: `.bss` becomes file-backed (rw PT_LOAD filesz=memsz ~0x1ace8).
2. One extra empty `R` PT_LOAD for the empty .init_array/.fini_array/.tdata/.tbss run.
3. riscv64 `.got` is 0x18 vs lld 0x20 (lld reserves the GOT[0] header slot).
4. aarch64 `.rodata` 0x388 vs lld 0x385 (tail alignment padding).
5. Archive-member order differs, so function addresses differ (same set, same sizes).
None of these stops a static image from loading, but 1 inflates the file and should
follow lld's orphan placement.

## Update 2026-11-19: divergences 1-3 fixed (verification-pending)
Root cause of 1: the SimpleOS user script names `.got : { *(.got) *(.got.*) }` after
`.data`; the engine ignored it (the synthetic GOT has no input sections) and appended
.got after .bss. Fix in `elf_boot_link.spl`:
- the synthetic GOT fills a script `.got` output section when one exists (fail closed if
  real input .got sections also land there); otherwise the old orphan position;
- riscv64 reserves ld.lld's one .got header slot (0 in a static image);
- an empty output section joins the current PT_LOAD (lld inherits flags), and a new
  PT_LOAD opens at relroEnd (first section after the last .got/init/fini/TLS one), as lld.
Spec: `elf_boot_link_got_spec` (fixtures `test/fixtures/linker/elf/got_orphan/`), oracle
= llvm-readelf of ld.lld 18. Re-run on the hello: riscv64 sections identical to lld,
both arches 4 PT_LOADs with identical RX/R/RW(data) and NOBITS .bss.
Still cosmetic: lld starts the .bss PT_LOAD at the empty .tbss boundary (same end
address); aarch64 .rodata tail padding (0x388 vs 0x385); archive member order.

## Plan: riscv64 U-mode filesystem launch (ready to pick up; kernel side not started)
Goal: OpenSBI (`-bios` fw_payload, never `-kernel`) -> SimpleOS S-mode kernel -> mount
NVFS -> load `/bin/hello` (sysroot-linked static ELF, base 0x100000000, Simple linker or
lld) -> run in U-mode -> its text and exit status on serial.

What exists (survey 2026-11-19, file:line):
- Spawn: `src/os/kernel/loader/riscv64_fs_exec_spawn.spl:205`
  (`riscv64_fs_exec_spawn_capture`) -> `fs_exec_spawn.spl:189` `fs_exec_prepare_spawn`
  -> `dispatch_fs_exec_user_handoff(Architecture.Riscv64)` (`:233`) ->
  `arch/user_entry_bridge.spl` -> `arch/riscv64/user_entry.spl` -> `_rv64_enter_user`.
- User context: `arch/riscv64/trap_model.spl:84` `create_rv64_user_context`
  (used at `context.spl:255`, `scheduler_context_bridge.spl:125`).
- Traps: `arch/riscv64/trap_vector.spl` saves frame -> `interrupt.spl:520`
  `rv64_dispatch_trap_frame_ptr`; U-mode ecall -> `syscall.spl:22` handler.
- Syscall ABI matches the sysroot: exit = id 0 (`syscall.spl:28`; crt0
  `simpleos-sysroot-riscv64.shs:166,173`), write = id 60 byte-wise
  (`syscall.spl:67-70`; libc `simpleos_libc.c:293`), id in a7
  (`src/os/libc/simpleos_syscall_riscv64.S:6,12`).
- Disk: `scripts/check/check-simpleos-riscv64-nvfs-qemu.shs` already boots OpenSBI ->
  U-Boot -> kernel with an NVFS root (`src/os/port/mkfs_nvfs.spl`) on virtio-mmio and
  reads files (`examples/09_embedded/simple_os/arch/riscv64/nvfs_root_entry.spl`).

Gaps:
- G1 unproven: `fs_exec_prepare_spawn` for Riscv64 maps PT_LOADs as Sv39 U pages at
  0x100000000 with a user stack (arm64 does it explicitly, `arm64_fs_exec_spawn.spl:101`).
- G2: no boot entry wires scheduler + stvec + NVFS + spawn on OpenSBI
  (`build_pid1_kernel_riscv64.shs` stops at `os_main_prepare_pid1`).
- G3: libc's second write path uses syscall id 32 (`simpleos_libc.c:297`); no id 32 case
  in `syscall.spl`.
- G4: no check script for a U-mode ELF on riscv64.

Steps (TDD each):
1. G1: unit spec feeding `fs_exec_prepare_spawn` a sysroot-linked hello ELF (fixture
   from this lane) and asserting U-page mappings at 0x100000000 and the user sp; fix the
   Riscv64 arm if RED.
2. G3: spec for id 32 -> implement in `syscall.spl` (or route libc to 60); repro both.
3. G2: new entry `examples/09_embedded/simple_os/arch/riscv64/fs_exec_hello_entry.spl`
   from `nvfs_root_entry.spl`: mount NVFS, init scheduler, set stvec to trap_vector,
   `riscv64_fs_exec_spawn_capture("/bin/hello")`, print `[fsexec] rc=<n>`.
4. Media: build hello with the sysroot (internal link and lld, both), stage at
   `/bin/hello` with `mkfs_nvfs`.
5. G4: `scripts/check/check-simpleos-riscv64-user-elf-opensbi.shs` on `-bios`
   fw_payload + NVFS disk; rungs: OpenSBI banner, hello's own text, `[fsexec] rc=7`;
   argv self-check bans `-kernel`/isa-debug-exit; selftest fixtures for each rung.
6. Run it for both linkers; record board path per board-runnable.md (same fw_payload +
   SD/NVFS image on a JH7110-class board).
Needs: the Rust seed (`SIMPLE_BIN`) to build the kernel until the self-hosted compiler can.

## Update 2026-11-19 (lane ssos-launch): G3 fixed, plan step 3 premise is wrong
- G3 (verification-pending): `syscall.spl` now backs id 32 Write for fd 1/2 (EBADF for
  other fds, EFAULT for a null buffer). Separate defect found and fixed in the same
  change: DebugWrite (id 60) called `rv64_process_stdout_write_byte(byte)` against the
  two-arg `(child_id, byte)` owner, so the id-60 path the sysroot libc uses for
  stdout/stderr could not compile. Spec `test/01_unit/os/kernel/arch/riscv64_syscall_write_spec.spl`
  covers the non-emitting paths (byte emission goes through the SBI console, which the
  hosted interpreter cannot run); emission must be proven by the OpenSBI rung (step 5).
- Step 3 cannot work as written: `riscv64_fs_exec_spawn_capture` ->
  `fs_exec_prepare_spawn` is a fail-closed stub that always returns pid -13, and
  `fs_exec_prepare_spawn_from_bytes` is also fail-closed (`spawn:auth-required`).
  This is policy (`smoke_entry.spl`: writable media without a loader-issued token is
  never entered). The only live route is the authenticated one
  (`riscv64_fs_exec_spawn_authenticated_capture_with_launch_v1`, driven by
  `riscv64_authenticated_media_acceptance_v1`), which needs the signed sidecars
  (`.MAN/.ADM/.SIG/.PUB`, `scripts/os/build_rv64_authenticated_hello.shs`, signing key
  inputs from `rebuild-sosix-qemu-media.shs`) staged on the boot media. G1 therefore
  lives in `adopt_authenticated_executable_pid_v1`, not `fs_exec_prepare_spawn`.
  Revised step 3: stage the sysroot hello plus its signed sidecars and go through the
  authenticated route; do not add an unauthenticated bypass.
- Kernel build from WSL via Windows `bin/simple.exe` (winlink.sh): all 753 modules
  compile (523 s), but the freestanding link fails with Windows os error 206 (command
  line > 32 KiB). See `windows_seed_freestanding_link_cmdline_too_long_2026-11-19.md`.
  No riscv64 kernel can be produced on this host until that is fixed and the seed
  redeployed (or a Linux seed is available in WSL).
