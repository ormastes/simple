# Native runtime guard allocation assumed 4 KiB pages

Status: fixed; focused native checks pass, canonical capsule verification follows
the reviewed commit. Host: macOS arm64, `getconf PAGESIZE` = 16384.

The core-C capsule failed its native memory-guard selfcheck because the C mirror
hardcoded a 4096-byte page. A 37-byte allocation placed its trailing guard at
offset 8192, which is not aligned to this host's pages. `mprotect` failed and
the allocator fell back to ordinary heap storage. Overflow/UAF protection was
absent and the double-free probe trapped. The unchanged parent capsule was
reproduced from `b9107f6d218f7e2e5d20be152744b8604c536781`: exit 1,
7.20 seconds, sampled process-tree peak 134336 KiB, quiescent cleanup.

`runtime_memory_guard.h` now caches POSIX `sysconf(_SC_PAGESIZE)` only when a
sampled allocation needs it. Failed discovery is cached without guessing a
page size. Checked division-first rounding rejects impossible mapping sizes
before multiplication or pointer arithmetic. The slot records its exact
mapping length, reused for whole-slot protection and quarantine eviction.
Windows remains on its existing unavailable-guard path.

Darwin reports protected-page access as SIGBUS as well as SIGSEGV. The three
guard selfchecks now recognize Darwin SIGBUS, while other hosts still require
SIGSEGV. Normal exits, aborts and unrelated signals remain failures. This is
supported by the real child crash report (`KERN_PROTECTION_FAILURE`, SIGBUS)
and [Apple's memory-access crash documentation](https://developer.apple.com/documentation/xcode/investigating-memory-access-crashes).
The corrected oracle linked to the unfixed parent archive still failed
(exit 133); signal portability cannot bless the broken allocation.

Evidence in `build/evidence/runtime-guard-pagesize/`:

- Standalone C contract with `-Wall -Wextra -Werror`: 4 KiB and 16 KiB layout,
  boundary rounding, SIZE_MAX/PTRDIFF_MAX rejection, cached discovery/failure,
  real host guard fault/UAF and quarantine eviction. PASS; 0.42 seconds,
  1425408-byte maximum RSS.
- Real `rt_mem_guard_native_selfcheck`, `rt_mem_guard_stale_slot_selfcheck`,
  `rt_mem_guard_after_sweep_selfcheck`: all PASS, respectively 0.35/0.35/0.39
  seconds and 1540096/1540096/1556480-byte maximum RSS. Combined focused rebuild
  and execution sampled tree peak 147776 KiB, quiescent cleanup.
- Disabled sampling decision compiled to byte-identical LLVM23 assembly
  before/after (SHA256 `3024d1f1c3ae443a39d1e5d469496ba2188dd72436338074f843fe860e501397`).
  No additional syscall, allocation or instruction is introduced on this path.
  Successful page caching adds one `size_t` per private translation unit;
  slot size and quarantine capacity are unchanged. Guarded virtual mappings
  scale with the required host page size; the broken fallback is not a valid
  guarded-performance baseline.

Independent Astra review found no must-fix issues. Both page sizes have layout
arithmetic coverage; live protection runs only on this 16 KiB macOS host. Linux
execution is unverified here. Existing slot-table synchronization and small
allocation alignment behavior are outside this focused fix. Sampled RSS is
not a kernel aggregate limit, and no bootstrap or release PASS is implied.
