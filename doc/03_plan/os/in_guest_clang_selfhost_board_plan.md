# Deep plan: LLVM/clang as a real FS executable on SimpleOS (board-runnable)

**Final goal (must):** clang runs as an on-disk FS executable on SimpleOS on real
board hardware, compiling a C file to an object it writes back to disk, retrievable
over SSH. QEMU is the dev harness; the board is the requirement. No design may depend
on a QEMU-only mechanism.

**Status (2026-07-12):** ✅ **FULL 2e COMPLETE.** All software increments done: clang compiles
`/hello.c`→`/hello.o` over real OpenSSH (Inc 1/2) and the object is retrieved BYTE-EXACT over
SSH via `ssh root@host getfile /hello.o` (Inc 3, `cd0418ee39cb`) — sha256 matches on-disk
`/HELLO.O`, host-links + runs == exit 7. Remaining is physical-hardware bring-up on the actual
mini-PC (NVMe/serial/NIC provable only there). Details below and in
`doc/03_plan/os/clang_over_ssh_2e_design.md`.

✅ **PHASE 1 DONE.** clang runs in ring-3 and COMPILES a C file:
`clang -cc1 -emit-obj -o /hello.o /hello.c` streams 124 MB clang → ring-3 → reads `/hello.c`
(28 B off NVMe) → serves `/dev/urandom` → writes a 712-byte `/hello.o` → exit(0). The object
is byte-valid: base64-dumped at exit, decodes to ELF64 `ET_REL`/`EM_X86_64` with a `main`
function symbol, **host-links and runs to `exit 7`** (== `int main(void){return 7;}`). Earlier
milestones: `clang --version` + exit(0) (391e3c6c6ab); abort-134 was a zero-sized heap from a
`.to_u64()` codegen bug (fixed). Input-lookup was a stale-image issue (a leftover
`stageD/hello.o` flips mkimg to the link pass, embedding `HELLO.O` not `HELLO.C`) — build the
image fresh for the compile pass. Next: Phase 2 (board port).

## Hard constraints (learned this session)

- **`-cc1` only, never the driver.** `clang -c` forks/execs a cc1 subprocess; ring-3 has
  no fork. Pass frontend args directly (from `clang_static -### -c hello.c`).
- **No in-guest linking in Phase 1.** `ld`/lld needs fork too. `.o` is the deliverable;
  link+run happens on host for verification, or is a later phase.
- **Decisive artifact = byte-valid `.o`, not "exit 0".** Verify: base64/disk `.o` →
  `llvm-readobj --file-headers --syms` = ET_REL/x86_64/`main` → host-link → run →
  `echo $?` == 7. Nothing less counts as done (session-long haiku blind spot).
- **Exit-path edits are highest-risk.** isa-debug-exit vs longjmp-resume is the exact
  bare-exec-flag interaction that broke both SSH gates before. Any change gates on BOTH
  `ssh_clang_hello_ring3.shs` AND `ssh_multi_cmd.shs` AND the clang path.
- **Board portability is unverifiable in-sandbox for physical I/O.** Validate what we can
  (OVMF = real UEFI firmware, zero isa-debug-exit dependency, `.o` on real NVMe) and state
  physical-hardware NVMe/serial/NIC as unvalidated-here honestly.
- One change per pass, trace-and-implement, review each. Discovery-first before implementing.

## Phase 1 — in-guest compile to a valid `.o` (QEMU; keep isa-debug-exit)

1a. **Input lookup (CURRENT BLOCKER):** clang opens `/hello.c`; image has `/HELLO.C`
    (cluster 3). Fix path resolution in the Stage D open handler / `fat32_find_file`
    (strip leading `/`, case-insensitive 8.3). Verify: `[sc] open path=/hello.c` →
    found, bytes served.
1b. **Iterate remaining syscalls** clang needs for a TU (read, fstat/newfstatat,
    mmap-of-file, lseek, getcwd, write, close, maybe clock/time), one per pass via the
    syscall trace. Expect a possible 2nd OOM (a TU needs >64 MiB); bump `HEAP_PAGES`
    if the heap is the limiter (QEMU has 2G) — trivial now that the heap is real.
1c. **Output capture:** clang creates `/hello.o` (O_CREAT/O_WRONLY), writes object bytes.
    Stage D already has an output-file RAM buffer + base64 dump at exit — exercise it.
1d. **Verify the `.o`:** decode → llvm-readobj ET_REL/x86_64/`main` → host `clang hello.o
    -o a.out && ./a.out; echo $?` == 7. This closes Phase 1.

## Phase 2 — board-runnable port (the must)

2a. ✅ **DONE (2026-07-12) — `.o` to real NVMe:** the bare-exec exit handler now calls
    `fat32_write_file(name, data, size)` for each RAMFS output; `/hello.o` is allocated a real
    free cluster (3807) and written to the NVMe disk image. Verified by parsing the raw image
    post-run: `HELLO.O` dirent → cluster 3807, 712 B → extracted bytes are ELF64 ET_REL
    EM_X86_64, host-link + run == exit 7 (byte-valid, identical result to 1d).
    Two harness fixes made this land: (i) `fsexec_mkimg_big.spl` reserves 16 spare clusters
    (512 KiB) so a free cluster exists; (ii) `build_clang_stream_ring3.shs` now parses
    `total_bytes=` from the mkimg stdout instead of a **stale, no-longer-written**
    `fat32-clang-total.txt` — the stale value truncated the image below BPB `total_sectors`,
    so the spare cluster's LBA fell 1 sector past EOF and the NVMe write was out-of-range
    (mark-EOC in the low FAT region passed; the high data-cluster write failed). Error-path
    `[wf-diag] … FAILED` serial markers left in `fat32_write_file` as board diagnostics.
2b. ✅ **DONE (2026-07-12) — board-safe exit:** the bare-exec exit (`_bare_exec_handle`
    case 0, the clang path) now prefers the kernel-resume savepoint — `if
    (rt_x86_ring3_resume_valid()) rt_x86_ring3_resume(rc)` — exactly like the SSH exit,
    with `outb 0xF4` + `cli;hlt` only as the standalone-smoke fallback. Verified: clang
    smoke logs `resume_valid=1` → `[spawn] ring3 program exited rc=0 (kernel resumed)` →
    `CLANG FILE-LAUNCH WORKS rc=0`, 0 faults; QEMU now exits via the entry's clean terminal
    (rc=1) not the mid-ring3 bare-exec fallback (rc=3). Also fixed a real board hazard:
    `rt_debug_exit_success` wrote `0xF4` then **returned** — on a board (0xF4 unused) that
    falls through past the caller's `main` → triple-fault; now it `cli;hlt` loops after the
    (QEMU-only) `0xF4`. SSH multi-cmd resume gate re-run green (no regression). Gate: both
    SSH gates + clang path green.
2c. ✅ **DONE (2026-07-12) — UEFI boot validation:** `ssh_ring3_uefi_boot.shs` boots the
    ring-3 kernel (with the 2b exit path compiled in) under REAL UEFI firmware — OVMF →
    GRUB (`grub-mkstandalone` BOOTX64.EFI) → multiboot → ExitBootServices → kernel `_start`
    — no QEMU `-kernel`. Green: `PRIMARY GATE PASS: sshd accept loop started under OVMF`,
    then over real OpenSSH `/FSEXEC.ELF` (a clang-BUILT ring-3 ELF loaded off the FS) prints
    `hello from clang on simpleos` + `[user] exit rc=42` → `UEFI BOOT VERIFIED`. This proves
    the kernel survives a real firmware memory-map handoff and runs an FS-exec ring-3 program
    to completion. Scope note (honest): this boots the SHARED ring-3 kernel; the clang-
    *compile* kernel (`fs_exec_clang_stream_ring3_entry`, 125 MB payload) uses the identical
    boot chain + ring-3 machinery — booting IT under OVMF and compiling `hello.c` is the 2e
    capstone, not re-proven here.
2d. ✅ **DONE (2026-07-12) — board robustness audit (no new code; verified graceful):**
    every unexpected path reports + degrades gracefully, none silently hangs or triple-faults:
    - **Ring-3 fault** (`spl_x86_on_user_fault`, interrupt.spl): emits `[fault] ring-3 process
      killed: SIGSEGV rip/cr2/cs` via fault-safe port I/O, then the rich-fault ISR parks the
      CPU (CS-guarded — the historical re-fault runaway is already fixed). Diagnostic + halt,
      no runaway.
    - **Unknown syscall** (`rt_syscall_dispatch` default): loud `[syscall] ENOSYS num=… a0=…`
      to serial + returns `-ENOSYS` to the ring-3 program (no hang).
    - **Unimplemented rt fn** (S0–S5/V0–V2 stubs): `FATAL: unimplemented rt function: <n>` +
      halt.
    - **FS write errors** (`fat32_write_file`): each failure prints a `[wf-diag] … FAILED`
      marker, `_fat32_free_chain`s any partial allocation, and returns `-1`.
    - **Exit terminal**: `rt_debug_exit_success` / bare-exec exit `cli;hlt` (2b) — no board
      fall-through.
    - **Overwrite (was the known gap) — now PROVEN:** re-ran clang on an image that already
      held `/hello.o`; `_fat32_find_root_dir_slot` reused the single dirent (no duplicate),
      the file moved to a fresh cluster (3807→3808), the **old cluster was freed** (FAT=0,
      no leak), and the extracted object host-links + runs == exit 7. Order is crash-safe:
      write-new → commit dir → free-old. Residual (not blocking): free-cluster search runs
      before freeing the old chain, so a same-size overwrite on a 100%-full disk would spuriously
      fail — fine here (16 spare clusters, one small file).
2e. ✅ **DONE (2026-07-12) — end-to-end over real OpenSSH:** `clang -cc1 -emit-obj -o /hello.o
    /hello.c` runs on the guest over SSH and writes `/hello.o` to the real NVMe disk (Inc 1/2:
    sshd shallow-frame tokenizes argv, `x86_64_fs_exec_spawn_heap` streams 124 MB clang into
    ring-3 post-net). `ssh root@host getfile /hello.o > retrieved.o` (Inc 3, `cd0418ee39cb`)
    returns the file bytes as channel stdout in one shot; retrieved.o is BYTE-IDENTICAL to the
    on-disk `/HELLO.O` (sha256 `d0c481d8…90a8c39b`, 712 B), ELF64 ET_REL, host-links + runs ==
    exit 7. Two x86_64-freestanding root-cause fixes shipped with Inc 3: `_build_channel_data_stable`
    now copies data via the `.push` intrinsic (the `rt_push_byte` reassignment form dropped the
    BYTE_PACKED representation for large arrays → 0x53-garbage payload, masked because small
    handshake packets stayed inline-packed); `_finish_exec_request_inline` binds `output.len()`
    to an intermediate var (chained `.to_u32()` mis-lowered → `consume_remote_window` dropped the
    payload). scp-source (`scp -O`) left near-complete (interactive ack handshake blocked by
    non-persisting nested-`me` mutation); `getfile` supersedes it. REMAINING: physical-hardware
    NVMe/serial/NIC bring-up, provable only on the actual mini-PC.

## Execution order

1a → 1b (loop) → 1c → 1d  (Phase 1 done: valid `.o`)  →  2a ✅ (.o on real NVMe)  →  2b ✅ (board-safe exit)  →  2c ✅ (UEFI boot)  →  2d ✅ (robustness)  →  2e ✅ (compile + byte-exact retrieve over SSH). ALL SOFTWARE DONE; physical-board bring-up remains.
Never start Phase 2 before 1d passes. Small model + guide per step; higher-model review +
the host-link-and-run / gate verification owned by the coordinator.
