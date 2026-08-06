# B1 witness: in-guest clang -cc1 aborts (SIGABRT/134) partway through a real TU — guest 64 MiB heap likely too small

Status: OPEN. Filed 2026-08-06, lane B1 (clang self-compile witness),
follow-up to `doc/08_tracking/bug/bare_in_cap_silently_truncates_guest_input_files_2026-08-06.md`.

## Summary

Booting SimpleOS under real OVMF UEFI firmware (never `-kernel` —
`.claude/rules/board-runnable.md`) and running the guest's freestanding
`clang -cc1` to compile the B1 witness TU
(`build/os/b1_witness/TU1.I`, preprocessed `llvm/lib/Support/DivisionByConstantInfo.cpp`,
1,164,308 bytes) now reads the **full, correct** file (the sibling
`bare_in_cap` truncation bug is confirmed fixed — see below) but the guest
process **aborts with exit status 134 (SIGABRT convention)** partway through
parsing, at line ~8061 of 17,567 — well before reaching the TU's own code.
The identical `-cc1` invocation on the host compiles cleanly and produces the
exact reference object.

## Two findings, not one

### 1. `bare_in_cap` truncation bug — CONFIRMED FIXED, not a new defect

The first B1 run this round hit exactly the truncation signature described in
`bare_in_cap_silently_truncates_guest_input_files_2026-08-06.md` (guest read
capped at exactly 1,048,576 bytes = 1 MiB = 32 clusters). Root-caused to a
**stale deployed kernel**, not a regression of the landed fix:

- `build/os/simpleos_ssh_ring3_uefi128.elf` (reused via `SKIP_KERNEL=1` for
  speed) had mtime `2026-08-06 06:00:42 UTC`.
- The fix commit `c3f5d82c9f1782ca12803ca4bb0cfa0d9d183e7e` landed at
  `2026-08-06 08:41:15 UTC` — 2.5 hours later.
- `strings` on the deployed kernel showed **zero** occurrences of the fix's
  new diagnostic string `"open EIO short read expected"`, proving the
  deployed ELF predated the fix.
- Independently verified the staged FAT32 image itself was never at fault:
  the on-disk data clusters and the FAT chain for `/TU1.I` (clusters
  3733..3768, 36 clusters) were byte-identical to the host reference and
  correctly linked (dumped and diffed directly from
  `build/os/elfexec_b1/fat32-b1.img`).
- Rebuilding the kernel from current source (`SKIP_KERNEL=0`) and rerunning:
  the guest log now reads `[vfs] open /TU1.I -> NVMe read 1164308 bytes` —
  the full file, exactly matching `TU1.I`'s real size. **Confirmed fixed.**

No action needed here beyond noting the trap for future B1/B-lane runs:
**always force a kernel rebuild** (`SKIP_KERNEL=0`) after any fix lands in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` or the
kernel source tree — a reused "proven" kernel binary can silently predate a
fix that only exists in source.

### 2. NEW: guest clang_static aborts mid-parse on a real TU — OPEN

With the fresh kernel, the exec ladder proceeds further than ever before but
the guest process still does not produce `/TU1.O`:

```
[vfs] open /TU1.I -> NVMe read 1164308 bytes
... (12 expected -Wuser-defined-literals warnings from libc++'s <chrono>, lines 8025-8061)
[syscall] exit status=134
[spawn] ring3 program exited rc=134 (kernel resumed)
```

No parse error, no clang diagnostic, no crash backtrace — the process simply
exits with status 134 (the guest libc's `SIGABRT` convention:
`src/os/libc/simpleos_libc.c:724` `void abort(void) { exit(134); }`, no
message).

**Host-side control (rules out flags/argv/environment):** the byte-identical
`-cc1` invocation run directly on the host —

```
clang++-20 -cc1 -triple x86_64-unknown-simpleos -emit-obj \
  -disable-free -clear-ast-before-backend -disable-llvm-verifier \
  -discard-value-names -main-file-name TU1.I \
  -mrelocation-model static -mframe-pointer=all \
  -fmath-errno -ffp-contract=on -fno-rounding-math -mconstructor-aliases \
  -funwind-tables=2 -target-cpu x86-64 -tune-cpu generic \
  -fdebug-compilation-dir=/ -fcoverage-compilation-dir=/ \
  -O3 -std=c++17 -fdeprecated-macro -ferror-limit 19 -fno-rtti \
  -fgnuc-version=4.2.1 -fskip-odr-check-in-gmf -vectorize-loops -vectorize-slp \
  -faddrsig -fno-ident -D__GCC_HAVE_DWARF2_CFI_ASM=1 \
  -o /tmp/host_repro.o -x c++-cpp-output build/os/b1_witness/TU1.I
```

— exits 0, emits the same 12 warnings (through the same line 8061), and
produces a 10,616-byte object whose sha256
(`f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`) is
byte-identical to the reference `TU1.O`. So the divergence is **guest-only**,
not a flag/argv/environment mismatch, not TU content, not a compiler-version
skew (R1 in the parent plan doc) — the host repro used the exact same 20.1.8
binary the reference was built with, so this doesn't even touch R1.

**Working theory — undersized guest heap.** The process crashes at line 8061
(`<chrono>`'s templated `operator""ns`/`operator""us` literals, the last of a
run of similar templated `operator""` definitions), a point in the TU that is
*earlier* than the target function bodies (`DivisionByConstantInfo::get`
starts much later) but is inside libc++'s heaviest templated preamble.
`abort()` is called from exactly two places relevant here
(`src/os/libc/simpleos_cxxabi.c:109,115`, both `operator new`/`operator
new[]` failure paths: "`new` must not return NULL (no exceptions)" — i.e.
`malloc()` returned NULL). The guest FS-exec heap-stream spawn path
(`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:412-413`,
`x86_64_fs_exec_enter_stream_heap_ring3`) maps a **fixed 64 MiB anonymous
heap** (`HEAP_PAGES = 16384`, `HEAP_PAGE_SZ = 4096`) for "real libc programs
like clang" — sized against the earlier proof-of-concept (`hello.c` → `puts`
→ exit 7), never validated against a real, template-heavy C++ TU. A full
-O3 libc++-templated C++17 compile routinely uses well over 64 MiB of heap
for AST + Sema + CodeGen state even for a TU this size; 64 MiB is a plausible
undersized guess, not a measured budget.

**Not yet done (next step, explicitly out of scope for this round):**
bumping `HEAP_PAGES` (and correspondingly the identity-mapped physical pool
in `ssh_ring3_clang_entry.spl`'s `pmm_init_identity_range(0x80000000,
0x100000, 0x18000000)`, currently 384 MiB total for the 122.6 MB clang_static
image + this heap + kernel state) and rerunning is the obvious next
experiment, but requires another kernel rebuild + full OVMF boot cycle and
was not attempted this round to avoid an unbounded investigation loop. If it
turns out heap size is not the cause, the next things to rule out are stack
depth (8 MiB guest stack, same file) and a genuine guest-libc/guest-libc++
correctness gap in the templated `<chrono>` literal operators specifically.

## Evidence

- Serial log: `build/os/ssh_b1_witness_uefi.serial.log` (full transcript from
  the `SKIP_KERNEL=0` rerun).
- Host repro object: sha256
  `f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`
  (byte-identical to `build/os/b1_witness/TU1.O`).
- Staging integrity: `build/os/elfexec_b1/fat32-b1.img`'s TU1 cluster region,
  extracted via `dd`, sha256-matches `build/os/b1_witness/TU1.I` exactly.
- Kernel provenance: rebuilt kernel used for the passing (full-file-read)
  run — `build/os/simpleos_ssh_ring3_uefi128.elf`, 975,632 bytes, built via
  `scripts/os/ssh_b1_witness_uefi.shs` with `SKIP_KERNEL=0`.

## What is NOT the cause (ruled out this round)

- FAT32 staging/write path — byte-identical on-disk, both data and FAT chain.
- The `bare_in_cap` 1 MiB truncation bug — confirmed fixed; the failure mode
  changed (full read now happens) once a freshly built kernel was used.
- `-cc1` flag set / argv / environment — host reproduces cleanly with the
  identical command line.
- TU content or compiler-revision skew (R1) — the host repro used the same
  20.1.8 binary as the reference and matches byte-for-byte; the guest crash
  happens on ordinary templated libc++ code common to any real C++ TU, not
  on anything specific to `DivisionByConstantInfo.cpp`.

## Infra landed alongside this investigation

- `src/os/port/llvm/sysroot.shs`: added `build_libcxxabi_runtime()` and
  `build_libunwind_runtime()` (libc++abi built from libcxxabi's own
  `LIBCXXABI_ENABLE_EXCEPTIONS=OFF` source list, `private_typeinfo.cpp` built
  with `-frtti` per libcxxabi's own CMakeLists convention since it implements
  the RTTI runtime itself; libunwind built from its own source list). Neither
  archive existed in the sysroot before this round, which blocked
  `clang_static.shs` entirely.
- `build/os/clang_static/bin/clang_static` (122 MB, statically linked,
  0 undefined symbols, entry at `0x40000000`) — built successfully for the
  first time this round via the now-complete sysroot.
- `scripts/os/fsexec_mkimg_b1.spl` — pre-existing from an earlier round, used
  as-is (unmodified).
- `scripts/os/ssh_b1_witness_uefi.shs` — new harness script, modeled on the
  proven `scripts/os/scp_retrieve_over_ssh_uefi.shs`, implementing the full
  stage → OVMF boot → `-cc1` compile → `getfile` retrieval → tier-1/tier-2
  compare pipeline from
  `doc/03_plan/os/simpleos/b1_clang_selfcompile_witness.md` §5.
