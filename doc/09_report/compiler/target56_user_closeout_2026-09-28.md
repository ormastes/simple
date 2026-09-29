# Target 5/6 isolated lane: user-accepted session closeout (2026-09-28)

Status: session closed by user; production verification is not PASS.

## Size reference decision

The Linux release-small NoGC hello limit remains 15,360 bytes and 1.05x C.
The C denominator is now the same-host, same-toolchain hello linked with the
same required startup wrapper, core runtime archive, linker options, section
GC, and strip policy. Bare C `main` remains an advisory comparison. The BS7
receipt now declares `c_reference_kind=matched-startup-v1`; the checker rejects
missing or altered declarations. This declaration still requires an actual
paired build and retained link provenance before production admission.

The retained matched pair has a 6,504-byte C-authored direct runtime writer
and 6,368-byte C `puts` entry: +136 bytes, or +2.1%. Both pass the 1.05x
diagnostic ratio, but neither is a current-source Simple hello. Bare C is
4,864 bytes, so the direct-writer probe is +1,640 bytes (+33.7%) against it.

## Commit review: performance and memory

Reviewed the isolated branch's source changes against its `origin/main`
merge base, with attention to literal print lowering, size-mode linking, the
cold HIR batch builder, warm package routing, and Git/SCV inventory refresh.

- The historical Stage2 Simple hello retained 526,433 bytes of zero-filled
  `.bss`, including the 524,288-byte literal intern table. The matched
  direct-writer probe retained 28 bytes of `.bss`, a 526,405-byte reduction
  in virtual static data. The branch's plain-literal lowering calls
  `rt_println_str` directly; the probe supports that memory-retention fix.
  Neither ELF imports `mmap`. `.bss` bytes are not a measured RSS reduction,
  and the current-source Simple hello still needs a build.
- The 30-pair historical Stage2 cold-HIR boundary diagnostic measured p95
  time 90,000 us versus 1,130,000 us and max RSS 27,972 KiB versus
  274,372 KiB. Ratios were 0.079646 and 0.101949; both improved for this
  isolated fixture. This does not cover production entrypoints.
- Warm package routing replaces repeated linear membership and selection
  scans with sorting, a queued set, and one entry-index pass. Its new lookup
  maps and per-entry index vector consume additional memory proportional to
  the reached graph. No current-source warm p95/RSS cohort exists, so a
  production regression or gain cannot be quantified.
- Inventory refresh still launches Git commands and enumerates untracked
  paths on warm requests. The new captured-HEAD change removes one redundant
  Git revision query and avoids mixed-revision event binding. It does not
  complete the persistent index's zero-scan warm path.

The BS7 synthetic checker fixture passed its clean path and six independent
rejection mutations after the reference change. `git diff --check` passed.
No current-source Stage4 hello, full Target 6 SPipe run, or production paired
time/RSS cohort passed. The tracked blockers and unfinished technical work
remain in `doc/08_tracking/todo/target5_target6_completion_2026-09-27.md`.
