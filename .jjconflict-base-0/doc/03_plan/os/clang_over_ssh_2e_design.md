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

## Progress (2026-07-12)
- **Inc 1 DONE + landed 0097ce77629.** clang compiles over real SSH via
  `x86_64_fs_exec_spawn_heap` → `.o` on real NVMe → exit 7 (raw-disk verified). All 3
  unknowns proven. Harness `scripts/os/build_clang_over_ssh.shs`.
- **Inc 2 IN PROGRESS (user chose full-deep = fix the root bug).** Root cause is a
  cranelift-backend char/text TAG-BOX codegen bug on `--target x86_64-unknown-none
  --backend cranelift`: `text.char_at(i)` returns a tag-boxed value (`0x12_0000_0001`),
  `starts_with` returns false, and `rt_string_from_byte_array(...)` stored into a field
  corrupts (11 B → 2 chars); `len()`/full-`==`/`[u8]`/`i64`/rodata literals are all fine.
  See `doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md`. Fixing it removes
  the raw-byte workaround AND unblocks Inc 3 (SFTP OPEN path decode). Worker digging the
  cranelift lowering (`src/compiler/70.backend/backend/cranelift_*.spl`).
- **Inc 3 DONE (getfile fallback):** `ssh root@host getfile /hello.o > retrieved.o` returns
  the raw file bytes as channel stdout in ONE shot (no interactive ack protocol, unlike
  scp-source). Server reads `/hello.o` off FAT32 (`_scp_read_file_bytes`, mmio_read8 raw-read
  idiom) and delivers it via `_finish_exec_request_inline`. Verified: `retrieved.o` is
  BYTE-IDENTICAL to the on-disk `/HELLO.O` (sha256 `d0c481d8…90a8c39b`, 712 B), ELF64
  ET_REL/EM_X86_64, host-links + runs == exit 7. Harness `scripts/os/scp_retrieve_over_ssh.shs`.
  TWO root-cause fixes landed with it:
  1. `_build_channel_data_stable`: the DATA copy used the `payload = rt_push_byte(payload, ..)`
     reassignment form, which on x86_64 freestanding drops the BYTE_PACKED representation once
     the array grows large and corrupts the payload (712-byte `/hello.o` delivered as
     0x53-garbage while small handshake/exit packets, staying inline-packed, delivered fine).
     Switched the data loop to the `.push` intrinsic (mutates in place, preserves packing) —
     same idiom `_copy_bytes_stable` already documents.
  2. `_finish_exec_request_inline`: the chained `output.len().to_u32()` mis-lowers on this lane,
     so `consume_remote_window()` saw a bogus huge count, rejected the payload, and silently
     dropped the channel data (empty `retrieved.o`). Bound the length to an intermediate var.
- **scp-source (`scp -O`) — near-complete, deferred:** the C-record + body path is built
  (`_scp_read_file_bytes`, `_scp_ctrl_line`, `_scp_step_inline`, now one-shot). TWO earlier
  diagnoses were DISPROVEN: (a) a "non-persisting nested-`me` mutation" (repro prints
  `NESTED_ME_OK`; `_finish_exec` mutates `self` via a nested `me` call and works); (b) a
  "chained `x.len().to_u32()` mis-lowering" (three standalone probes + a real-code revert all
  pass — see the retracted
  `doc/08_tracking/bug/x64_freestanding_chained_len_cast_miscompile.md`). The genuine defect in
  this whole arc was the `rt_push_byte` reassignment dropping BYTE_PACKED for large `[u8]`
  (fixed with `.push`; `doc/08_tracking/bug/x64_freestanding_push_byte_reassign_byte_packed.md`).
  The remaining scp-source factor is only that each `scp`/`ssh` invocation opens a fresh
  connection (new `SshSession`, `scp_stage=0`). `getfile` supersedes scp for retrieval, so
  scp-source is left as-is.
