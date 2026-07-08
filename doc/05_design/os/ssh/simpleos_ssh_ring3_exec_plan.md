# SimpleOS — one-shot SSH → ring-3 filesystem-exec: execution plan

Status: 2026-07-08. The OS-side execution path (run a clang-built ELF from the
FAT32 filesystem in ring-3 to clean exit) is **DONE and verified** — see
`scripts/os/build_clang_hello_ring3.shs` and
`project_simpleos_clang_hello_fs_ring3`. This doc is the ordered checklist to
close the remaining transport gap: **`ssh guest <cmd>` executes an on-disk ELF in
ring-3 over a real SSH connection** (one-shot: the program exits and takes QEMU
down; success is proven on the serial log).

## What already works (do not rebuild)

- Ring-3 FS-exec loader: `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`
  (`x86_64_fs_exec_enter_image_ring3`) — PML4[0]-safe mapping, SysV frame, ring-3.
- Shell-facing spawn: `src/os/kernel/loader/x86_64_fs_exec_spawn.spl`
  (`x86_64_fs_exec_spawn`) ← `fs_exec_spawn_ring3` (`fs_exec_spawn.spl`). Reads the
  ELF from FAT post-vmm via `_x86_64_read_spawn_bytes_and_blob`
  (`stream_open`+`stream_read_at`+`mmio_read32` validate).
- Kernel prereqs (landed this session): `EFER.NXE` (cpu.spl), `environ` (crt0.S),
  native `exit` syscall (baremetal_stubs.c case 0), NVMe-BAR-post-vmm
  (`vmm_map_nvme_bar_high()` after `vmm_init`, verified by the prod entry reading
  POST-vmm — the shell's read ordering).
- SSH login + auth: proven earlier; sshd is pure-Simple under `src/os/apps/sshd/`.
- virtio-net: PIO-based (`baremetal_stubs.c` `_vnet.iobase`), guest IP 10.0.2.15,
  QEMU host `127.0.0.1:2222` → guest `:22`.

## The gap (two separate kernels today)

- SSH boot `examples/09_embedded/simple_os/arch/x86_64/ssh_live_entry.spl` does
  ONLY `rt_net_init()` + `SshDaemon.new(22).start()` — **no nvme/vmm/ring-3**.
- Ring-3 boot `fs_exec_prod_ring3_entry.spl` does nvme+vmm+bar-high+ring-3 but
  **no networking/sshd**, and is one-shot.
- SSH exec dispatch (`ssh_session_channel.spl:213 _do_live_interactive_fast_path`,
  L241/L244/L260) matches 3 fixed strings (`true`,
  `simple.smf --version; simple --check`) and otherwise routes to a **text
  reporter** `ssh_exec_fat_launch_line` (`ssh_session_shell_test_ext.spl:56`) that
  resolves a path but **never spawns**. No sshd code calls `fs_exec_spawn_ring3`.
- Path resolution mismatch: the SSH resolver uses the **app registry**
  (`app_registry_cached_bytes`), but the loader reads **FAT**. A real on-disk
  `/FSEXEC.ELF` must be routed to `fs_exec_spawn_ring3(path)` (FAT read), not the
  registry check.

## Execution checklist (one-shot demo)

1. **[MEDIUM] Fork a ring-3-capable SSH entry.** New
   `arch/x86_64/ssh_ring3_entry.spl` = `ssh_live_entry.spl` + the prod init
   sequence BEFORE `SshDaemon.start()`: `arch_x86_64_early_init()` +
   `rt_x86_tss_init()` + `simpleos_nvme_init()` + `rt_net_init()` +
   `pmm_init_identity_range(...)` + `vmm_init(g_pmm,0)` + `vmm_map_nvme_bar_high()`.
   Keep `rt_net_init` BEFORE `vmm_init` so net comes up under boot page tables.
2. **[EMPIRICAL — the one risk] Verify virtio-net survives `vmm_init`.** PIO ports
   survive the PML4 swap, but the rx/tx DMA ring RAM must fall inside what
   `vmm_init` maps (0..4GB identity). Boot the forked entry, confirm sshd still
   handshakes AFTER `vmm_init`. If net drops: mitigation = receive the exec command
   PRE-`vmm_init`, then run nvme+vmm+bar+spawn (session drops; serial proves it).
   There is no `vmm_map_virtio_net_bar_high` today — add one only if PIO/DMA proves
   MMIO-dependent.
3. **[SMALL] Route the exec dispatch to a real spawn.** In
   `ssh_session_channel.spl _do_live_interactive_fast_path`, for a command that
   resolves to a FAT path, call `fs_exec_spawn_ring3(path, argv, [])` (import from
   `os.kernel.loader.fs_exec_spawn`) instead of `ssh_exec_fat_launch_line`. Resolve
   the path to a FAT location (accept an absolute `/…ELF` directly; or extend
   `_ssh_shell_resolve_launch_path` to probe FAT via the loader read rather than
   the registry). On spawn success control never returns.
4. **[SMALL] Stage the ELF on disk + a test harness.** Bake the clang hello onto
   the SSH boot's disk as `/FSEXEC.ELF` (reuse `patch_fsexec_image.spl`); a
   `scripts/os/ssh_clang_hello_ring3.shs` that boots the forked entry under QEMU
   with `-netdev user,hostfwd=tcp::2222-:22` + the NVMe disk, then host-side
   `ssh -p 2222 root@127.0.0.1 /FSEXEC.ELF` (needs `sshpass`/key). Gate on the
   serial log: `hello from clang on simpleos` + `[user] exit rc=42`.
5. **[LARGE — defer] Interactive shell / return-to-scheduler.** For a persistent
   shell (multiple commands over one SSH session), ring-3 exit must return to the
   scheduler instead of `isa-debug-exit`. Not required for the one-shot demo.

## Risk summary

Dominant effort = items 1+3 (mechanical). The single ballooning risk = item 2
(net-survives-`vmm_init`), which is empirical and has a known mitigation. Item 5
is the only genuinely large piece and is out of scope for `ssh guest run /ELF`.

## Empirical results — verified 2026-07-08

Item 1 (fork) and item 2 (net survives `vmm_init`) are **PROVEN**, and a new
prerequisite blocker was found:

- **Forked entry `arch/x86_64/ssh_ring3_entry.spl` BUILDS** (merged kernel:
  sshd + net + nvme + vmm + ring-3 loader, `build/os/simpleos_ssh_ring3.elf`,
  22 MB, 0 failed). Native-build recipe + build-marker generation
  (`build/os/generated/ssh_live_build_marker.spl`, not auto-written for x64 —
  gap in `os_build_run.spl:203`, riscv64-only) captured.
- **BOOTS and sshd LISTENS after `vmm_init`** — serial:
  `[boot] pmm+vmm online (+nvme bar high)` → `[sshd] SSH daemon listening on
  port 22` → `[sshd] accept loop start`. So **virtio-net (PIO) survives
  `vmm_init`** (item 2 resolved — no `vmm_map_virtio_net_bar_high` needed).
- **TCP + version-banner exchange WORK**: a real host `ssh -p 2222
  root@127.0.0.1 true` connects; `[tcp] Connection established`, `[sshd] accepted
  client`, banner sent, client version `SSH-2.0-OpenSSH_9.6p1` received.

**NEW BLOCKER (prerequisite, not the exec wiring): x64 SSH LOGIN itself fails at
version exchange** under freestanding native-build — the server reads an empty
client version and aborts. Filed:
`doc/08_tracking/bug/x64_sshd_version_exchange_freestanding.md` (double-take
consumes the buffered version + boxed-`[u8]` read-back). x64 SSH login has never
passed (only rv64 is proven), so this must be fixed BEFORE item 3 (exec dispatch)
is demonstrable end-to-end. Once x64 SSH login works, item 3 (route resolved path
→ `fs_exec_spawn_ring3`) + item 4 (harness) complete the one-shot demo; the
OS-side ring-3 exec they drive is already proven.
