# Deep plan: LLVM/clang as a real FS executable on SimpleOS (board-runnable)

**Final goal (must):** clang runs as an on-disk FS executable on SimpleOS on real
board hardware, compiling a C file to an object it writes back to disk, retrievable
over SSH. QEMU is the dev harness; the board is the requirement. No design may depend
on a QEMU-only mechanism.

<<<<<<< Conflict 1 of 2
+++++++ Contents of side #1
**Status (2026-07-13, corrected):** clang compiles `/hello.c`→`/hello.o` over real OpenSSH
(Inc 1/2) and the object is retrieved BYTE-EXACT via `ssh root@host getfile /hello.o` (Inc 3,
`cd0418ee39cb`) — sha256 matches on-disk `/HELLO.O`, host-links + runs == exit 7. **This is
proven under QEMU `-kernel` only.**

⚠️ **OPEN GAP — the 2e capstone is NOT yet met (violates the plan's own "no QEMU-only
mechanism" rule).** The clang-*compile* kernel (`fs_exec_clang_stream_ring3_entry`, 125 MB
payload) has NEVER booted under OVMF/UEFI (the board proxy). 2c proved OVMF boot for the SMALL
(~2 MB) hello kernel only. Root cause = a hard linker-layout conflict, NOT physical hardware:
- GRUB-EFI/OVMF's multiboot1 relocator requires the kernel loaded HIGH (128 MB / `0x8000000`)
  so the low region `[1MB,128MB)` stays free for its trampoline — else `#UD` at RIP~`0x1012`
  before `_start` (see `linker_low1mb.ld` base comment).
- The clang ring-3 payload is linked at VA `[0x10000000, 0x16100000)` in the user AS. A 128 MB
  kernel base pushes kernel `.bss` to ~375 MB, OVERLAPPING that payload range, so the syscall
  path (user cr3) faults writing kernel `.bss`. Hence the clang kernel is forced to the 1 MB
  base — `-kernel`-only ("Not for GRUB-EFI"). The two constraints are mutually exclusive under
  the current flat layout.

**Fix path (2f — required to close the goal, software-only, QEMU-provable via OVMF):** make the
clang kernel OVMF-bootable WITHOUT overlapping the payload. Options, cleanest first:
- (a) **Direct UEFI-stub entry** (`efi_main`, `--target x86_64-unknown-uefi`) that loads the
  kernel via UEFI boot services and jumps to `_start` — no multiboot1 low relocator at all, so
  the kernel can load anywhere and payload VA is unconstrained. Best match for real board UEFI.
- (b) **Higher-half kernel** (`0xffffffff80000000`) + a tiny low trampoline, decoupling kernel
  placement from the payload's low-canonical VA.
- (c) **Relocate the clang payload VA** out of `[0x10000000,0x16100000)` (re-link `clang_static`
  higher, or use PIE) so a 128 MB kernel base no longer overlaps.
Gate: `fs_exec_clang_stream_ring3_entry` boots under OVMF, `ssh root@host clang -cc1 … /hello.c`
writes `/hello.o` to NVMe, `getfile` retrieves it byte-exact — with NO QEMU `-kernel`, NO
`isa-debug-exit`. Only THEN is 2e/board-runnable actually met (plus physical-hardware bring-up).

**2f RESOLVED (2026-07-13, commit `7cf0b6aec3a`):** took extended option (c). Ground-truthing
the ELFs showed the streaming kernel carries a 211 MB NOBITS `.bss` (`_kernel_end`≈0x0e412000),
so at a 128 MB base its band [0x08000000, ~0x16400000] swallowed BOTH the payload
(`clang_static` [268 MB, ~352 MB]) and the mmap base (0x10000000). Fix: relocate payload VA
0x10000000 → 0x40000000 (1 GiB) via `src/os/port/llvm/sysroot.shs` simpleos.ld, and mmap base
→ 0x50000000 (1.25 GiB) via `src/os/kernel/ipc/syscall.spl`; both now clear the `.bss` band.
Only low-half user regions are payload/mmap/brk (brk 0x30000000 already above the band), so this
is a complete fix — (b)'s boot-assembly rework was unnecessary. New `linker_128mb.ld` (OVMF
kernel variant, base 0x08000000) + `scripts/os/scp_retrieve_over_ssh_uefi.shs` (OVMF pflash
getfile harness, no `-kernel`). Verified under OVMF: GRUB-EFI → multiboot → ring-3 sshd accept
loop (overlap fault cleared) → in-guest `clang -cc1 -emit-obj /hello.o` → getfile 712-byte
ET_REL/EM_X86_64 object → host `cc && ./a.out` → exit 7.

Remaining after 2f: physical-hardware bring-up on the actual mini-PC (NVMe/serial/NIC provable
only there). Detailed phased plan (P0 board+evidence channel → P1 USB first-light → P2 real
NVMe compile → P3 real NIC driver [the HIGH gap: only virtio-net exists] → P4 full goal):
`doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`. Details below and in
`doc/03_plan/os/clang_over_ssh_2e_design.md`.

✅ **PHASE 1 DONE.** clang runs in ring-3 and COMPILES a C file:
%%%%%%% Changes from base to side #2
-**Status (2026-07-12):** ✅ **FULL 2e COMPLETE.** All software increments done: clang compiles
-`/hello.c`→`/hello.o` over real OpenSSH (Inc 1/2) and the object is retrieved BYTE-EXACT over
-SSH via `ssh root@host getfile /hello.o` (Inc 3, `cd0418ee39cb`) — sha256 matches on-disk
-`/HELLO.O`, host-links + runs == exit 7. Remaining is physical-hardware bring-up on the actual
-mini-PC (NVMe/serial/NIC provable only there). Details below and in
-`doc/03_plan/os/clang_over_ssh_2e_design.md`.
-
-✅ **PHASE 1 DONE.** clang runs in ring-3 and COMPILES a C file:
+**Status (2026-07-12):** ✅ **PHASE 1 DONE.** clang runs in ring-3 and COMPILES a C file:
>>>>>>> Conflict 1 of 2 ends
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
2e. **End-to-end board scenario:** over real OpenSSH, `clang -cc1 -emit-obj -o /hello.o
    /hello.c` on the guest writes `/hello.o` to disk; retrieve over SSH/scp; verify. Mark
    physical-hardware NVMe/serial/NIC as provable only on the actual mini-PC.

## Execution order

<<<<<<< Conflict 2 of 2
+++++++ Contents of side #1
1a → 1b (loop) → 1c → 1d  (Phase 1 done: valid `.o`)  →  2a ✅ (.o on real NVMe)  →  2b ✅ (board-safe exit)  →  2c ✅ (UEFI boot)  →  2d ✅ (robustness)  →  2e ✅ (compile + byte-exact retrieve over SSH, QEMU `-kernel`)  →  2f ✅ (clang kernel boots under OVMF — the board-proxy capstone; payload/mmap relocated clear of the 128 MB kernel `.bss` band, commit `7cf0b6aec3a`)  →  physical-board bring-up. All software done; only physical-hardware bring-up on the actual mini-PC remains.
%%%%%%% Changes from base to side #2
-1a → 1b (loop) → 1c → 1d  (Phase 1 done: valid `.o`)  →  2a ✅ (.o on real NVMe)  →  2b ✅ (board-safe exit)  →  2c ✅ (UEFI boot)  →  2d ✅ (robustness)  →  2e ✅ (compile + byte-exact retrieve over SSH). ALL SOFTWARE DONE; physical-board bring-up remains.
+1a → 1b (loop) → 1c → 1d  (Phase 1 done: valid `.o`)  →  2a ✅ (.o on real NVMe)  →  2b ✅ (board-safe exit)  →  2c ✅ (UEFI boot)  →  2d ✅ (robustness)  →  2e.
>>>>>>> Conflict 2 of 2 ends
Never start Phase 2 before 1d passes. Small model + guide per step; higher-model review +
the host-link-and-run / gate verification owned by the coordinator.
