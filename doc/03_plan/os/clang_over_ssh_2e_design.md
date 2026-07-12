# Phase 2e — clang compile over SSH → retrieve `.o` (design)

Goal (user-approved "Full 2e", 2026-07-12): over real OpenSSH, run
`clang -cc1 -emit-obj -o /hello.o /hello.c` on the guest, write `/hello.o` to the
real FAT32/NVMe disk, retrieve it over SSH/scp on the host, and verify it
host-links + runs == exit 7.

Everything else in the goal is already DONE + landed (2a `.o` on NVMe, 2b board-safe
exit, 2c UEFI boot, 2d robustness). 2e is the SSH-invocation capstone.

## What already works (reuse, do NOT rebuild)
- `x86_64_fs_exec_enter_stream_heap_ring3(path, hdr_blob, hdr_len, file_len, argv, envp)`
  — streams the 124.6 MB clang per-PT_LOAD into ring-3 + a 64 MiB user heap. Proven
  at BOOT (clang-stream smoke): compiles `/hello.c` → `/hello.o` on NVMe, exit 7.
- sshd deferred spawn from the SHALLOW accept-loop frame: `_sshd_run_pending_ring3_exec`
  calls `x86_64_fs_exec_spawn("/FSEXEC.ELF", …)` DIRECTLY (not the mis-dispatching @cfg
  `fs_exec_spawn_ring3` wrapper — that routes to the VFS reader → len=0). Multi-command
  SSH proven (MULTI-COMMAND SSH WORKS, kernel-resumed=2).
- Raw-disk `.o` extraction (host python: BPB → FAT → dirent → clusters) — the verifier.

## The three real unknowns (prove increment 1 FIRST, per advisor)
1. **FAT stream post-net:** `x86_64_fs_exec_spawn_as` documents a bug
   (`x64_ssh_kernel_fat32_stream_open_zero`): after `rt_net_init`+vmm+SSH activity the
   exec-time FAT/NVMe read returns 0, so small ELFs are PRELOADED at boot while state is
   pristine. clang is 124 MB — it can NOT fit the static path-read buffer (≈4 MiB), so
   preload is impossible; it MUST stream at exec time. Does `simpleos_fat32_stream_open` /
   `stream_read_at` work post-net? (clang boot smoke streams PRE-net, so untested here.)
2. **pmm pool size:** the clang boot entry does its OWN `pmm_init_identity_range(0x80000000,
   0x100000, 0x18000000)` = 384 MiB pool for the 124 MB payload + 64 MiB heap. The SSH
   kernel's pmm is initialized by boot for normal programs — is there ≥ ~200 MB free at
   SSH-exec time? Requires QEMU `-m 2G` (SSH gate already uses 2G).
3. **heap-spawn from the shallow frame:** `enter_stream_heap_ring3` sets `_bare_exec_mode`
   (rt_user_heap_init). The 2b work made the bare-exec exit resume the savepoint — so a
   clang exit from the accept-loop frame should longjmp back like `/FSEXEC.ELF` does. Verify.

## Increment plan (prove the unknown, then decorate)
- **Inc 1 (critical unknown):** add `x86_64_fs_exec_spawn_heap(path, argv, envp)` in
  `x86_64_fs_exec_spawn.spl` — mirror the stream branch of `x86_64_fs_exec_spawn_as` but
  call `enter_stream_heap_ring3` (stream, never preload). Wire a SECOND sshd command that
  calls it DIRECTLY with hardcoded clang `-cc1 … /hello.c` argv. Stage clang on the SSH
  image (a `build_clang_over_ssh.shs` harness: SSH kernel + clang + hello.c on one FAT32
  image, virtio-net hostfwd). GATE: serial shows clang runs + `[oo-nvme] persist /hello.o
  -> OK` + kernel resumes; verify by raw-disk `.o` extraction == exit 7. If pmm/stream
  fails here, fix THAT (file a bug) before any decoration.
- **Inc 2:** parse the real SSH command string → path + argv (so `ssh root@host clang -cc1
  … /hello.c` drives it, not a hardcode). Keep the x86_64-direct-spawn rule.
- **Inc 3:** retrieve `/hello.o` over scp/SSH on the host; verify host-link + run == 7.
  Mark physical-HW NVMe/serial/NIC as provable only on the real mini-PC.

## Verify discipline
`.o` proven by raw-disk extract → `llvm-readobj` (ET_REL/EM_X86_64/main) → `cc .o -o a &&
./a; echo $?` == 7. NOT "exit 0". Land exact bytes via plumbing FF push (drift-guarded,
SSH key). Agents implement + report serial; coordinator reviews + lands.
