# Simple linker: static links call an IFUNC's resolver instead of the function

- id: simple_linker_static_ifunc_calls_resolver
- status: verification-pending
- area: src/compiler/70.backend/linker/elf (elf_static_link, new iplt.spl)
- found: 2026-11-18 armv7 static-glibc link (memcpy is STT_GNU_IFUNC)

## Symptom
A static (non-PIE ET_EXEC) link resolved every reference to a defined
STT_GNU_IFUNC symbol to the symbol's own value, which is the resolver. A call then ran the resolver
and used the returned function pointer as the result. This was a silent
miscompile on all ELF targets: no IPLT, no IRELATIVE and no
`__rel[a]_iplt_start/end`. It surfaced on armv7 as `R_ARM_JUMP24 against
'memcpy': branch target is not 4-byte aligned` (the resolver is Thumb code).
x86_64/aarch64 static glibc were never exercised against this.

## Fix
`linker/elf/iplt.spl` (shared): per referenced IFUNC, one 16-byte IPLT entry
plus an IGOT slot (initially the resolver), and an IRELATIVE entry in
`.rela.iplt` (x86_64 37, aarch64 1032) or `.rel.iplt` (i386 42, ARM 160).
Synthetic `__rela_iplt_*` / `__rel_iplt_*` cover that section, matching the
weak names glibc's static libc.a expects (checked with llvm-nm).
`elf_static_link` redirects relocations and GOT slots to the entry. ARM entries
have a Thumb prologue (`bx pc; nop`) at +0 for Thumb branches and ARM code at +4.
Static ET_EXEC only (ponytail: PIE needs PIC stubs + IRELATIVE in .rela.dyn).

## Evidence
- `test/01_unit/compiler/backend/linker/iplt_spec.spl` 6/6 (failed first:
  module missing). elf_static_link / elf_got_static / elf_static_pie specs pass.
- Freestanding IFUNC test (`slk/ifunc.c`, `ifunc_start.c` walks the iplt
  table like apply_irel): Simple and ld.lld both print "hi" with rc=42 under qemu-user on
  x86_64, aarch64, i686 and armv7.
- armv7 static glibc hello now links (431228 B). The IFUNC tables in it are
  well-formed: `.rel.iplt` has 2 entries and `__rel_iplt_*` brackets it. It still SIGSEGVs at run time
  inside `_dl_debug_vdprintf`, glibc's early fatal-error printer, while the ld.lld
  build of the same inputs prints "hello libc 1 tls=8". So startup aborts for a
  reason outside IFUNC (next to triage: static TLS/TCB setup, `.ARM.exidx`).
  Tracked as a remaining armv7-static item.
- Time and RSS: an aarch64 dynamic hello link takes 9.0 s / 542 MB peak WS on the branch vs
  8.6 s / 517 MB on origin (Windows seed). The output is identical (5160 B).
  elf_link_rss_budget.shs not run: its native bench driver needs a heavy
  native build, which is disallowed while the p2 bootstrap runs.

## Remaining
- x86_64/aarch64 static glibc: the staged sysroots lack compiler-rt builtins and
  libunwind (`__letf2`, `_Unwind_Resume`, `__aarch64_*` outline atomics).
- i686 static glibc: `__letf2`/`__unordtf2` are absent from compiler-rt i386
  (no TF mode). A Simple soft-float implementation is waiting on a user decision.
