# B1 witness: in-guest clang -cc1 aborts (SIGABRT/134) partway through a real TU — heap-size hypothesis DISCONFIRMED

Status: RESOLVED as far as B1 requires (2026-08-06, fourth follow-up round).
The SIGABRT crash is root-caused and fixed — `-cc1` now compiles `TU1.I` to
completion in-guest with no abort, every run, 3 for 3, producing a valid
ELF64 relocatable of the exact correct size. The originally-planned win
condition (byte-identical `TU1.O` vs a reference built with **stock Ubuntu**
clang-20.1.8, sha256
`f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`) is
**not** met, but Round 4 root-caused why: that reference was never built
with the project's own LLVM fork (the compiler `clang_static` actually is),
so byte-identity against it was never a sound oracle. Disassembly proves the
entire `.text` diff is one functionally-equivalent instruction-selection
choice (`tzcnt`-trick vs `bsf`+`cmovne` for `countTrailingZeros`) in a single
function, not a correctness bug. See "Round 3" for the crash fix and "Round
4" for the `.text`-diff root cause, the oracle-script correction, and an
inconclusive host-native-fork-compiler side finding filed for follow-up.

Status (historical, rounds 1-2): OPEN. Filed 2026-08-06, lane B1 (clang self-compile witness),
follow-up to `doc/08_tracking/bug/bare_in_cap_silently_truncates_guest_input_files_2026-08-06.md`.
**Update 2026-08-06 (same day, follow-up round):** the "undersized 64 MiB
heap" theory below (§2) was tested and DISCONFIRMED — see
"Heap-bump experiment result" at the end of this doc. The guest still
SIGABRTs at the **exact same source line** (`TU1.I:8061`) after an 8x heap
increase (64 MiB -> 512 MiB), and heap utilization at the crash point was
~28 MiB either way, nowhere near either capacity. Root cause is still open;
leading candidate is now guest **stack** depth (8 MiB, unchanged), not heap.

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

## Heap-bump experiment result (2026-08-06, same day follow-up)

Bumped `HEAP_PAGES` in
`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:413` from `16384` (64 MiB) to
`131072` (512 MiB) — an 8x increase, safely within budget: the identity pool
backing `pmm_alloc_page_raw()` spans the full `pmm_init_identity_range(0x80000000, ...)`
= 2 GiB (matches `QEMU_MEM=2G`), not just the 384 MiB kernel/clang_static
reservation, and the heap VA (`0x9000000000`) is a disjoint high-canonical
region from clang's link range and stack. Rebuilt the kernel fresh
(`SKIP_KERNEL=0`; confirmed `build/os/simpleos_ssh_ring3_uefi128.elf` mtime
09:25 UTC, after the 09:23 UTC source edit) and reran
`scripts/os/ssh_b1_witness_uefi.shs` end-to-end under real OVMF UEFI.

**Result: crash point is byte-for-byte identical to the pre-bump run.**
`build/os/ssh_b1_witness_uefi.serial.log` shows the same 12
`-Wuser-defined-literals` warnings for `TU1.I` lines 8028-8061 (the
`<chrono>` templated `operator""h/min/s/ms/us/ns` literal definitions), then
`[syscall] exit status=134` / `[spawn] ring3 program exited rc=134`
immediately after the line-8061 warning — same line, same warning count, same
immediate-abort position as the original 64 MiB run.

**Heap was nowhere near exhausted at the crash point either way.** The
guest's `[heap] alloc sz=... off_before=... off_after=...` trace shows only
4 allocations total before the abort, ending at `off_after=0x1c15790` =
~28.15 MiB — far under both the old 64 MiB cap and the new 512 MiB cap. An
8x capacity increase with ~28 MiB actually in use at crash time, and zero
change in crash location, is strong evidence the abort is **not caused by
`operator new` returning NULL from heap exhaustion** at this point in the
TU, contradicting the working theory in §2 above.

(Caveat: the `[heap] alloc` trace's source could not be located in
`src/**` in this round — it may be gated to log only large allocations, so it
is not proof small mallocs stayed low too. But the identical-crash-line
result alone, independent of that trace, already disconfirms heap size as
the controlling variable: doubling capacity 8x moved nothing.)

**Status:** heap-size hypothesis in §2 is DISCONFIRMED as the root cause
(the 64 MiB -> 512 MiB bump is still landed as a real, harmless robustness
improvement — a real C++ TU compile should not be running that close to any
heap ceiling regardless — but it does not fix B1). The abort is a hard
`abort()` from `src/os/libc/simpleos_cxxabi.c:109,115`
(`operator new`/`operator new[]` returning NULL), called from *somewhere*
immediately after parsing/instantiating the 12th and last templated
`operator""` chrono literal at exactly `TU1.I:8061`, every time, regardless
of available heap. Candidates not yet ruled out:

- **Guest stack overflow, not heap.** The guest stack is a fixed 8 MiB
  (`STACK_PAGES = 2048` in `x86_64_fs_exec_ring3.spl:360`), unchanged by this
  experiment. A stack-overflow write into an adjacent guard/unmapped page
  could plausibly be misreported as the `operator new` NULL-return abort path
  if the guest's exception/fault handler routes an unhandled fault through
  the same `abort()` call, or if `operator new`'s own internal recursion (via
  libc++abi's exception-handling machinery, even with `-fno-rtti`) blows the
  stack at exactly this point — the 12 templated `operator""` definitions in
  a row is exactly the kind of repetitive template-instantiation load that
  can build stack depth in `Sema`/`CodeGen` recursion.
- **A genuine guest libc/libc++ correctness gap specific to this construct**
  (e.g. mis-sized allocator metadata, a corrupted heap header from an earlier
  allocation triggering a false NULL/overflow check on the *next* alloc
  regardless of total capacity — this would explain "same line every time,
  independent of heap cap" just as well as a stack overflow would).

**Not yet done, explicitly deferred to avoid an unbounded investigation
loop:** instrumenting the guest abort path to print which of the two
`abort()` call sites and file:line fired would immediately distinguish these
theories from further heap-cap changes; next lane should start there rather
than trying larger heap sizes again — this experiment shows that axis is
exhausted as a lever.

## Round 3 (2026-08-06, same day, second follow-up): instrumented, root-caused, fixed

### What each candidate `abort()` site actually guards (verified from source, not guessed)

Read `src/os/libc/simpleos_cxxabi.c` directly. Both of the two sites named in
Round 2 are `operator new` / `operator new[]` NULL-return aborts — **not**
stack-guard-page trap handlers, confirming (not just guessing) the doc's own
"working theory" language from Round 2:

- `_Znwm(unsigned long size)` = `operator new(size_t)`:
  `void *p = malloc(size); if (!p) abort();`
- `_Znam(unsigned long size)` = `operator new[](size_t)`: same pattern.

Two other `abort()` sites exist in the same file, both print a message before
aborting: `__cxa_pure_virtual` ("pure virtual method called") and
`__stack_chk_fail` ("*** stack smashing detected ***"); `__assert_fail` also
aborts after an `fprintf`. `abort()` itself
(`src/os/libc/simpleos_libc.c:724`, `void abort(void) { exit(134); }`) is the
single implementation reached by all of these and was the only place a raw,
unattributed `exit(134)` could originate from in this codebase — confirmed by
grepping every `abort(` call site in `src/os/libc/*.c`.

### Instrumentation added

Added an `fprintf(stderr, ...)` diagnostic (matching the file's existing
unbuffered `fprintf(stderr,...)`/`write()` convention — `write()` for fd 1/2
routes byte-by-byte through `simpleos_syscall(60, ...)` i.e. serial
`DebugWrite`, with **no libc-level buffering**, so nothing is lost even if
`abort()` fires immediately after) at both `_Znwm` and `_Znam`, printing the
requested size, plus a second diagnostic at the true `abort()` implementation
itself (`simpleos_libc.c:724`) printing `__builtin_return_address(0)` so an
abort reached through any *other*, non-printing path (e.g. a raw internal
`abort()` call inside libc++/libc++abi/LLVM) could still be symbolized.

### First rebuild/rerun: a real but misleading null result — stale `clang_static`

The first fresh kernel rebuild + OVMF rerun reproduced the exact same
`exit status=134` at `TU1.I:8061`, but **printed neither new diagnostic** —
appearing to rule out both named `abort()` sites entirely. Investigation
before trusting that result: `build/os/clang_static/bin/clang_static`
(122 MB, statically linked, the guest binary that actually runs `-cc1`)
had mtime **09:00:26 UTC**, more than 50 minutes **before** the libc edits
landed (09:53/09:57 UTC) — the harness's `SKIP_KERNEL=0`/`SKIP_STAGE=1`
knobs rebuild the *kernel* and re-copy an *already-built* `clang_static`
into the FAT32 payload, but never rebuild `clang_static` itself from source.
This is the same "stale deployed binary" trap already on record for the
kernel earlier the same day
(`src/os/libc/libsimpleos_c.a` was independently confirmed stale too, mtime
06:21 UTC). **Always rebuild `libsimpleos_c.a` (`cd src/os/libc && make`),
copy it into `build/os/sysroot/lib/libsimpleos_c.a`, and relink
`clang_static` (`sh src/os/port/llvm/clang_static.shs`) after any guest-libc
source edit** — the B1 harness alone does not do this.

### Second rebuild/rerun: root cause found

After rebuilding `libsimpleos_c.a` and relinking `clang_static` (confirmed via
`strings build/os/clang_static/bin/clang_static | grep -c` showing both new
diagnostic strings present, count=2) and rerunning under real OVMF UEFI, the
serial log (`build/os/ssh_b1_witness_uefi.serial.log`) showed, immediately
after the same 12th `-Wuser-defined-literals` warning at `TU1.I:8061`:

```
[cxxabi] _Znwm (operator new) abort: malloc(0) returned NULL at simpleos_cxxabi.c:109
[abort] simpleos_libc.c:724 abort() called, caller ra=0x447d7105
[syscall] exit status=134
[spawn] ring3 program exited rc=134 (kernel resumed)
```

**`_Znwm` (`operator new(size_t)`) fired, with `size=0`.** Neither candidate
theory from Round 2 (heap exhaustion, stack overflow) was correct — the
process aborts because clang/libc++ makes a **zero-byte `operator new`
call** (plausible during Sema/CodeGen bookkeeping for the 12 templated
`<chrono>` `operator""` literal definitions just parsed) and the guest's
`operator new` treats that as allocation failure.

**Root cause:** `src/os/libc/simpleos_dlmalloc.c:134`:
`if (size == 0) return NULL;` — a legal C `malloc(0)` behavior (POSIX permits
either NULL or a unique valid pointer). But `_Znwm`/`_Znam` in
`simpleos_cxxabi.c` delegated straight to `malloc(size)` with no size-0
special case, and C++ `[expr.new]` **requires** `operator new` to never fail
for a size-0 request — it must return a non-null, distinct pointer. The
guest's `operator new` was silently violating that guarantee, and this
particular TU is the first B1-lane input that happens to trigger a
zero-size `new` during compilation.

### Fix

`src/os/libc/simpleos_cxxabi.c`, `_Znwm` and `_Znam`: added `if (size == 0)
size = 1;` before the `malloc()` call (the standard idiom — bump to a
minimal nonzero request so `operator new` always gets a valid, distinct
pointer for size 0, exactly mirroring how `_ZnwmSt11align_val_t` already
delegates to the now-fixed `_Znwm`). The nothrow variants
(`_ZnwmRKSt9nothrow_t`/`_ZnamRKSt9nothrow_t`) were left unchanged — nothrow
`new` is permitted to return null, and `TU1.I` does not exercise that path.

### Verification

Rebuilt `libsimpleos_c.a`, relinked `clang_static` (0 undefined symbols),
reran the full harness under real OVMF UEFI (kernel ELF confirmed genuinely
`ELF64` via `readelf -h | grep Class`, picking up the linker fix from commit
`7c9609333fd04fc48900c14ca2d60d479fb448e6` landed earlier the same day).
Result, reproduced twice in a row (`b1_run4`, `b1_run5`):

```
  [ok]   L4 in-guest clang -cc1 compiled /TU1.O under OVMF
```

— no abort, `-cc1` runs to completion. Serial log confirms
`[oo] name=/TU1.O size=10616` and `[oo-nvme] persist /TU1.O -> OK`, matching
the reference object's exact size. **The SIGABRT crash is fixed.**

### Win condition: NOT fully met — new, narrower, non-crashing defect

The harness's SSH `getfile` retrieval step failed both times
(`FAIL: retrieved_TU1.O missing or empty (transport failure — see doc §5
known hazard)`) even though the guest's own log shows the full 10,616 bytes
were served (`[sshd-session] getfile path=/TU1.O fsize=10616 bytes=10616`) —
a separate, pre-existing SSH-transport issue, out of scope for this bug.
Since `/TU1.O` was persisted to the NVMe-backed FAT32 image
(`build/os/elfexec_b1/fat32-b1.img`) before QEMU exited, it was extracted
directly from the image (FAT32 BPB parsed: `bytes_per_sector=512`,
`sectors_per_cluster=64`, `reserved_sectors=32`, `fat_count=1`,
`sectors_per_fat32=38` → `data_start=35840`, `cluster_size=32768`; `/TU1.O`
at `cluster=3` per `scripts/os/simpleos_fat32_image_list.spl` →
`offset=68608`), read as 10,616 bytes, valid `ELF 64-bit LSB relocatable,
x86-64`.

sha256 of the extracted object: `7b6b6a3db45a3150f362b44d64623b9fd1104b17ae8ba8efcee36146087bfc6f` —
**does NOT match** the reference `f71aa3f9545c908c3e0b3bc3eddf4d1b11bde443152e45a04207b8969252cfb4`.
Running `build/os/b1_witness/compare_object.shs` (tier-2 section-by-section
diff) on the extracted object against the reference:

```
TIER1 FAIL — not byte-identical. Falling through to tier-2 analysis.
  .text DIFF  ref=0987ca12bbb8c0d135acd722b802105b45599f4bb0cffa9396b44aa522f7b61f guest=8627904bb4f75b93426dfb598c1ac60d0bcf3e5bdada4f508aed7757ce1fa277
  .rodata SAME
  .data SAME
  .bss SAME
  .llvm_addrsig SAME
```

Same size, `.rodata`/`.data`/`.bss`/`.llvm_addrsig` byte-identical — only
`.text` differs. This is a **new, narrower, non-crashing defect**: the guest
now compiles the TU to completion but its codegen output diverges from the
host's for the same flags/TU/compiler build. Candidates, not yet
investigated: guest-vs-host floating-point/`long double` codegen
differences (relevant given the crash-adjacent code was `<chrono>`'s
`long double`-based literal operators), instruction-selection nondeterminism
tied to the guest's memory layout, or a real remaining guest-specific
codegen bug. **Not yet root-caused — filed here as the next B1-lane
follow-up rather than investigated further this round**, to avoid repeating
the "unbounded investigation loop" this doc's earlier rounds explicitly
called out.

### Files changed this round

- `src/os/libc/simpleos_cxxabi.c` — `_Znwm`/`_Znam` size-0 fix (the actual
  bug fix) + diagnostic `fprintf` at both sites.
- `src/os/libc/simpleos_libc.c` — diagnostic `fprintf` with caller return
  address at the `abort()` implementation.

### Evidence (this round)

- Serial logs (this session's scratchpad,not committed):
  `b1_run3.log` (pre-fix, shows the `[cxxabi] _Znwm ... malloc(0)` diagnostic
  firing), `b1_run4.log`/`b1_run5.log` (post-fix, both show L4 passing).
- `build/os/ssh_b1_witness_uefi.serial.log` — full transcript of the last
  (`b1_run5`) run.
- Extracted post-fix object sha256:
  `7b6b6a3db45a3150f362b44d64623b9fd1104b17ae8ba8efcee36146087bfc6f`
  (10,616 bytes, valid ELF64 relocatable) — NOT a match to the win-condition
  reference; see ".text DIFF" analysis above.

## Round 4 (2026-08-06, follow-up): `.text` DIFF root-caused — wrong-compiler reference, not a guest bug

### The "R1 ruled out" claim in Round 3 was never actually tested

Round 3 states TU/compiler-revision skew (R1) was ruled out because "the host
repro used the exact same 20.1.8 binary the reference was built with." That
statement is true but answers the wrong question. Reading
`build/os/b1_witness/make_reference.shs:10` directly:
`CC1BIN=${CC1BIN:-/usr/lib/llvm-20/bin/clang}` — the reference `TU1.O` (and
the Round 3 "host repro" that matched it byte-for-byte) were **both** built
with the stock **Ubuntu llvm-20 package** (`20.1.8`,
`87f0227cb601`, dated 2025-08-04). Neither one ever invoked the project's own
LLVM fork. The actual in-guest compiler, `clang_static`, is linked from a
**different** LLVM tree entirely:
`github.com/ormastes/llvm-project.git`, branch `simpleos`, currently at
commit `59612206386553df81efc06ec0421acf646d49ef` (`20.0.0git`, dated
2026-08-06) — confirmed via `git -C /home/ormastes/llvm-project log -1`. So
the Round 3 control tested "is the reference generator deterministic"
(yes), not "does the fork's compiler match the reference" — R1 was
mislabeled ruled-out; it was never exercised.

### Disassembly diff: the entire `.text` DIFF is one 3-byte instruction-selection difference

`build/os/b1_witness/compare_object.shs`'s tier-2 loop only diffs the *base*
`.text` section by name; this TU has several COMDAT `.text.<mangled>`
sections too (`readelf -SW` confirms), but those are all byte-identical —
only the base `.text` (5,145 vs 5,148 bytes, +3) differs. Full
`llvm-objdump-20 -d --no-show-raw-insn` diff of that section (guest object
extracted from `build/os/elfexec_b1/fat32-b1.img` cluster 3, matching the
already-recorded sha256 `7b6b6a3d...`) against the reference `TU1.O` shows
**exactly one semantic divergence**, inside
`_ZN4llvm30UnsignedDivisionByConstantInfo3getERKNS_5APIntEjb` (confirmed via
`readelf -sW`: size `3353` (ref) vs `3356` (guest), the same +3; every other
symbol identical) — a `countTrailingZeros` idiom at ref-offset `0x11e1`:

```
ref:    movl $0x40, %ebx ; tzcntq %rax, %rbx                (10 bytes)
guest:  bsfq %rax, %rcx ; movl $0x40, %ebx ; cmovneq %rcx, %rbx  (13 bytes)
```

Both are correct, standard x86 lowerings of "count trailing zeros, defined
as 64 when the input is zero": the reference's form pre-loads the
destination with 64 and issues `tzcnt` (which decodes as `rep bsf` on
non-BMI hardware and, per real-silicon behavior, leaves the destination
unmodified when the input is zero — the classic BMI-independent `tzcnt`
trick); the guest's form is the more conservative explicit `bsf` +
`cmovne` fallback. **Semantically equivalent, not a correctness bug.** Every
other byte in every other diff line downstream is the same instruction with
addresses shifted by the constant +3 propagating through relative jump
targets — confirmed by diffing corresponding operand mnemonics line-by-line,
not just addresses. `.rela.text` was not independently diffed by content
(same-size relocations at shifted offsets are expected and consistent with
this).

**Classification: wrong-compiler reference artifact, not a guest bug**,
per the advisor's framing — byte-identity against a *different compiler
build* (Ubuntu's stock clang-20.1.8) was never a sound oracle for "does
`clang_static` (the project's own LLVM fork) compile this TU correctly
inside SimpleOS." What B1 actually demonstrates stands on its own: the
guest process now compiles a real, large (1.16 MB) C++17 TU to completion
under real OVMF UEFI with no crash, producing a valid ELF64 relocatable of
the exact correct size with byte-identical `.rodata`/`.data`/`.bss`/
`.llvm_addrsig`, and the sole `.text` divergence disassembles to one
functionally-equivalent instruction-selection choice.

### Attempted host-native fork-compiler control — inconclusive, a second finding surfaced

To get a genuine apples-to-apples reference (same fork commit, run natively
on the host instead of through the guest OS), a host-native build of the
fork already exists:
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20` — confirmed via
`--version` to be `clang version 20.0.0git
(https://github.com/ormastes/llvm-project.git
59612206386553df81efc06ec0421acf646d49ef)`, i.e. the identical commit
`clang_static` was built from, `make_reference.shs`'s own `$CROSS_BUILD`
tree, dynamically linked against the host's normal glibc (not
`simpleos_dlmalloc`/`simpleos_cxxabi`).

Running the identical `-cc1` line from `make_reference.shs:23-32` with this
binary **also aborts, exit 134, at the same source position** (last warning
at `TU1.I:8061`). This was investigated in some depth to check whether it
duplicates the original guest bug (it should not, by hypothesis, since
`operator new(0)` never returns NULL on glibc):

- `strace -f` shows a literal `exit(134)` **syscall**, not a raw
  signal — confirmed against a ground-truth `abort()` test binary on the
  same host, which instead shows `tgkill(...SIGABRT...)` /
  `+++ killed by SIGABRT (core dumped) +++`. So this is *not* the same
  failure mode as a real `abort()`/SIGABRT.
- `/usr/bin/time -v` shows Maximum RSS 62,976 KB (~63 MB) and
  "Signals delivered: 0" — rules out OOM and rules out a delivered fatal
  signal.
- `gdb -batch -ex run -ex bt` shows `exited with code 0206` (octal 134) with
  **no stack to unwind** — gdb saw a clean process exit, not a trap/signal
  stop, so no backtrace could be captured this way.
- Ruled out as the cause: `ulimit -s 65536` (8x default stack, still
  crashes), dropping `-vectorize-loops -vectorize-slp` (still crashes),
  `-fsyntax-only` (succeeds, 0 warnings-only, rc=0 — so Sema/parsing of the
  templated `<chrono>` `operator""` literals is fine; this is an `-O3`
  codegen-only failure). No `LLVM ERROR:`/`bad_alloc`/assertion message
  appeared anywhere in stderr despite the binary having assertions compiled
  in (`strings` shows `Assertion failed: %s at %s:%u (%s)`).
- Grepped the fork source (`llvm/lib/Support/Unix/Signals.inc`,
  `clang/tools/driver/cc1_main.cpp`, `CrashRecoveryContext.cpp`) for a
  literal `134`/`Process::Exit` pattern that would explain a deliberate
  self-chosen exit code matching SimpleOS's own `abort()` convention;
  found none. The exact internal call site that invokes `exit(134)` is
  **not identified**.

**This does not contradict the documented guest success.** The guest run
(`b1_run5`, this same fork commit, same TU, same flags, executed via
`clang_static` under real OVMF UEFI) is independently verified to have
produced a complete, correctly-sized, valid object — re-confirmed in this
round by directly disassembling the extracted `TU1_extracted.O` cleanly.
Since the natively-run fork binary crashes here but the guest binary (same
fork commit) does not, the most likely explanation is that this specific
sandboxed host shell has some restriction (a seccomp/ptrace policy,
resource-limit, or environment difference invisible to `ulimit`/cgroup
inspection performed above) that this particular `-O3` compile path is
sensitive to — **not** a reproduction of the original guest bug, and not
proof the fork's backend is broken. **Not chased further this round** to
avoid an unbounded loop (per the standing rule on this doc); flagging for a
follow-up lane to retest `build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang-20`
outside any agent sandbox before drawing conclusions from it.

### In-scope fix landed this round: `compare_object.shs` oracle correction

The script's own header comment is self-contradictory: it claims tier-2
requires "identical `.text`" *and* separately says any diff "must be
attributable to ... revision skew" — a revision skew can, and here does,
change `.text`. It also claims to check `.rela*` content but the loop never
does. Rewrote the tier-2 header comment and section list to state plainly
that `.text`/`.rela.text` MAY legitimately differ under a same-effect,
different-encoding instruction-selection change from a different compiler
build, and that such a diff requires a disassembly-level review (not a
sha256-only gate) before being accepted. `TU1.O` was **not** regenerated or
swapped — it remains the correct byte-identical output of its own generator
(`make_reference.shs` with the stock Ubuntu `clang-20`); it was simply never
a sound byte-for-byte oracle for the fork compiler and the script's
comments now say so.

### Evidence (this round)

- Guest object (already on record): sha256
  `7b6b6a3db45a3150f362b44d64623b9fd1104b17ae8ba8efcee36146087bfc6f`.
- Fork commit confirmed twice: `git -C /home/ormastes/llvm-project log -1`
  and `clang-20 --version` from the cross-build tree, both
  `59612206386553df81efc06ec0421acf646d49ef`.
- `readelf -SW` section-header diff: only `.text` size differs
  (`0x1419` vs `0x141c`), all other sections byte-identical.
- `readelf -sW` symbol-table diff: only
  `_ZN4llvm30UnsignedDivisionByConstantInfo3getERKNS_5APIntEjb` size differs
  (`3353` vs `3356`), all other symbols identical.
- `llvm-objdump-20 -d` diff of `.text`: single instruction-selection
  divergence at the countTrailingZeros idiom, everything else is address-shift
  propagation of that one +3.
