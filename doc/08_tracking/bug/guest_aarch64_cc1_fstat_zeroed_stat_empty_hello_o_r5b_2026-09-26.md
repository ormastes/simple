# R5b: in-guest-linked /HELLO2.ELF is a hollow green — guest libc fstat zeroed-stat starves cc1's input read

Date: 2026-09-26
Lane: lane-C1 aarch64 in-guest clang compile (scripts/qemu/check_simpleos_arm64_clang_compile.shs)
Owner: lane-C1 (this repo kernel shim + guest toolchain lane /home/yoon/llvm-project-simpleos)
Found by: agent-45, R5b cycle (route B lane-local handoff)

## Summary

The R5 gate (`rung=R5-run-hello2 rc=0` + `CLANG_IN_GUEST_ARM64_OK`) was a
HOLLOW green: the in-guest lld's /HELLO2.ELF ran and exited 0, but its
`printf("HELLO_C_FROM_GUEST_ARM64")` never reached serial — no DebugWrite
(syscall 60) chars and no write(1) SVC between `eret to EL0` and exit.

Root cause is NOT in the in-guest lld and NOT in crt0. It is upstream,
in the guest cc1's INPUT read: the guest libc's `fstat` was a lane-local
**zeroed-stat stub** (`memset(buf,0,sizeof *buf); return 0;` — the R3-era
RECORDED adaptation in build-os-llvm/scripts/sysroot-mirror-aarch64.shs).
clang's `MemoryBuffer::getOpenFile` trusts `st_size`: with the fd stat
reading 0 it builds an EMPTY buffer WITHOUT issuing any read syscall, so
the guest cc1 compiled an EMPTY translation unit from /HELLO.C and wrote
a 696-byte object with `.text` size 0 (no `main`, no rodata). The in-guest
lld then linked a product with no real `main`: crt0's `bl main` bound to
the libc archive's WEAK `main_shim.o` stub (`b _Z4mainiPPc`, undefined
weak → lld fallthrough into the next symbol, `__cxa_atexit`), which
returned 0 → `exit(0)`. Hollow green, byte-exact.

## Evidence chain

1. Guest RAM-table dump (QEMU monitor `memsave` of `g_svc_ram_files`):
   `/HELLO.O` = 696 B, and the object is degenerate —
   `llvm-objdump -h`: `.text` size 0; symtab has only the `HELLO.C`
   file symbol. No `main`, no `.rodata` string.
2. Guest SVC trace (run-20260926_154351): cc1 `open("/HELLO.C")` → fd 3
   (kernel FAT resolve `cluster=11 size=108`), then NO `id=31` read for
   fd 3 anywhere before `R4a rc=0`. clang fstat'd fd 3, read size 0,
   never read.
3. In-guest product (payload-region memsave, 110,408 B): `main` is
   `w F .text 00000004` at 0x100000f0 — the 4-byte weak shim stub;
   `bl main` at crt0's 0x100000b0 lands there; the stub branches to
   0x100000f4 `<__cxa_atexit>` (the undefined-weak fallthrough). No
   `bl printf`/`bl puts` anywhere; the string `HELLO_C_FROM_GUEST_ARM64`
   is ABSENT from .rodata. The whole .text after 0x100000f0 is the
   correct host link's text shifted down by 24 bytes (28-byte real main
   replaced by the 4-byte stub).
4. Host-reproduced link (same-version host-cross clang-20 -cc1 +
   host-cross lld, identical CRT0.O/LIBC.A/SIMPLEOS.LD, base 0x10000000):
   110,400 B, `main` strong at 0x100000f0 calling `printf` at 0x10004b08,
   string present. Correct — so the divergence is in the guest-side
   INPUTS, and the only input that differs is the guest cc1's HELLO.O
   (696 B degenerate vs 1104 B real).
5. Fork guest-libc source (build-os-llvm/libc-build-aarch64/simpleos_fs.c:55):
   `int fstat(int fd, struct stat *buf) { memset(buf, 0, sizeof(*buf)); return 0; ... }`
   — the unreachable real body below is the repo's syscall fstat.

## Why the R3-era stub existed (and why its rationale was wrong here)

The stub was added (df464042524d) because the arm64 user-svc table then
had no id-34 stat, so every fstat returned ENOSYS and LLVM hard-failed
(Process::FixupStandardFileDescriptors treats errno != EBADF as fatal).
The comment claimed "st_mode=0 is not regular_file, so LLVM takes
getMemoryBufferForStream (reads to EOF — always correct)". That is true
for LLVM's stdio STREAMS but FALSE for clang's input-file path:
MemoryBuffer::getOpenFile with st_size=0 builds an empty buffer and never
reads. R3 (banner, no input files) worked; R4a silently compiled nothing.

## Fix

1. Kernel (this repo, examples/09_embedded/simple_os/arch/arm64/boot/
   baremetal_stubs.c): `arm64_svc_file_stat` now takes a3 and honors
   fd-mode (a3=1, the repo libc fstat's convention): file fds get the fd
   table's tracked size; stdio fds 0/1/2 keep the zeroed stat (R3-proven);
   unknown fds get -EBADF. Dispatch passes a3. The repo libc's fstat
   already syscalls `simpleos_syscall(34, fd, 0, buf, 1, 0)` — no libc
   source change needed (comment updated).
   MODE CHOICE (second iteration): the file-fd stat must carry the real
   size with a NON-regular mode. A regular (S_IFREG) mode routes LLVM's
   getOpenFileImpl into shouldUseMmap for files >= 16 KiB, and the guest
   kernel's mmap is anonymous-only — it hands back zeroed pages, so the
   relinked lld read a zeroed /LIBC.A ("error: /LIBC.A: unknown file
   type", gate run-20260926_162227). With a non-regular mode LLVM takes
   getMemoryBufferForStream (read-to-EOF) for every size — the same path
   the pre-fix lld used to read its inputs correctly. The guest mmap is
   never invoked for MemoryBuffer.
2. Guest toolchain (fork, branch simpleos, 0fead4889fc4): drop the fstat
   zeroed-stub sed patch from build-os-llvm/scripts/sysroot-mirror-aarch64.shs;
   the repo's real syscall fstat is the source of truth. libc-build-aarch64
   working copy synced; simpleos_fs.o rebuilt (fstat now does the syscall),
   swapped into sysroot-aarch64/lib/libsimpleos_c.a; guest clang-20 + lld
   relinked (clang-20 fstat verified: `bl simpleos_syscall`, id 34 a3=1).

## Verification

See the lane status doc — the gate boot with the fix shows the guest cc1
reading /HELLO.C (id=31 reads on fd 3), a real HELLO.O, and the R5
product printing HELLO_C_FROM_GUEST_ARM64 on serial.
