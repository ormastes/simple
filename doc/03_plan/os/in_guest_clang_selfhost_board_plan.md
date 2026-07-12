# Deep plan: LLVM/clang as a real FS executable on SimpleOS (board-runnable)

**Final goal (must):** clang runs as an on-disk FS executable on SimpleOS on real
board hardware, compiling a C file to an object it writes back to disk, retrievable
over SSH. QEMU is the dev harness; the board is the requirement. No design may depend
on a QEMU-only mechanism.

**Status (2026-07-12):** ✅ **PHASE 1 DONE.** clang runs in ring-3 and COMPILES a C file:
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
2c. **UEFI boot validation:** boot the clang-capable kernel+disk under OVMF via
    `ssh_ring3_uefi_boot.shs` (real UEFI firmware path), proving no multiboot/QEMU-`-kernel`
    dependency.
2d. **Robustness for the board:** every syscall/FS error path recovers + reports instead of
    hang/triple-fault (so an unexpected situation on hardware degrades gracefully, not a
    silent halt). Audit the fault handler + syscall default cases.
    - **Known gap (2026-07-12):** `fat32_write_file` on a **pre-existing** `/hello.o` is
      untested — 2a used a fresh image each run. A second clang run (or a board disk that
      already holds the file) hits the dir-slot reuse / cluster-free-then-realloc path. Test
      overwrite + truncate-shorter/grow-longer before trusting it on hardware.
2e. **End-to-end board scenario:** over real OpenSSH, `clang -cc1 -emit-obj -o /hello.o
    /hello.c` on the guest writes `/hello.o` to disk; retrieve over SSH/scp; verify. Mark
    physical-hardware NVMe/serial/NIC as provable only on the actual mini-PC.

## Execution order

1a → 1b (loop) → 1c → 1d  (Phase 1 done: valid `.o`)  →  2a ✅ (.o on real NVMe)  →  2b ✅ (board-safe exit)  →  2c → 2d → 2e.
Never start Phase 2 before 1d passes. Small model + guide per step; higher-model review +
the host-link-and-run / gate verification owned by the coordinator.
