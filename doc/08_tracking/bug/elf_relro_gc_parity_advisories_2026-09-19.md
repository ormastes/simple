# Internal ELF linker: three RELRO / GC parity gaps found by adversarial review

- **Filed:** 2026-09-19 (lane C1 review, `work/lnk-c1`)
- **Status:** OPEN — parity gaps, each bounded and none a mis-link of the
  inputs the in-tree fixtures cover
- **Component:** `src/compiler/70.backend/linker/elf/{elf_static_link,gc_sections}.spl`
- **Fixed in the same review (not part of this record):** output `sh_entsize`
  on mixed inputs (now 0 when inputs disagree, ld.lld `commitSection`),
  `elf_merge_piece_off` out-of-range offsets (now a named Err), and the
  SHF_MERGE default rejecting valid C (now demoted to unmerged).

## 1. RELRO membership omits `.bss.rel.ro`, `.ctors`, `.dtors`, `.jcr`

`elf_is_relro_input` (`elf_static_link.spl`) covers `.data.rel.ro`,
`.init_array`, `.fini_array`, `.preinit_array`, plus `.dynamic` and `.got`.
ld.lld's `isRelroSection` also covers `.bss.rel.ro`, `.ctors`, `.dtors` and
`.jcr`.

Adding them to the RELRO rank alone would NOT be enough, which is why this is
filed rather than patched: `elf_out_name` maps a writable PROGBITS `.ctors` /
`.dtors` / `.jcr` input into `.data`, and a NOBITS `.bss.rel.ro` into `.bss`,
so those names never reach the output. Closing this means giving them their own
output sections first (ld.lld keeps `.ctors`/`.dtors`/`.jcr` as themselves and
`.bss.rel.ro` inside the RELRO region), then ranking them with the other RELRO
members. No in-tree fixture produces them (modern clang emits `.init_array`),
so the gap is currently unobservable in the specs — which is exactly why it is
written down.

## 2. GC roots omit ld.lld's `includeInDynsym` set

`elf_gc_live` roots are `isReserved` plus the entry symbol. ld.lld also roots
every section defining a symbol that is exported to `.dynsym`
(`includeInDynsym`: `--export-dynamic`, a shared-object build, a
`--dynamic-list`, or a symbol needed by a DSO). This linker exports nothing
from an executable's `.dynsym` (it holds imports only) and cannot build shared
objects, so today the set is empty and the two agree.

It is masked twice over: `gc_sections` additionally rejects any allocatable
`.eh_frame`, and every dynamic-libc link in the tree carries one, so GC is not
even reachable for the links where an export set could exist. When either the
`.eh_frame` reject or shared-object output lands, this root must land with it,
or a dynamically-reachable definition will be silently collected.

## 3. A static x86_64 exec whose GOT relaxed away emits no `.got` and no RELRO

With `pic_start_x64.o` + `pic_lib_x64.o` every `REX_GOTPCRELX` relaxes to
`lea`, so `sc.got_keys` is empty and no `.got` section is created; ld.lld still
emits a zero-sized `.got` and a `PT_GNU_RELRO` covering it. The binaries are
equivalent (an empty region protects nothing) but the segment shape differs,
and any tooling that keys on "has RELRO" sees a difference. Fixing it means
emitting `.got` unconditionally for the modes where ld.lld does, which changes
segment counts for several existing specs — deliberately not done inside the
RELRO commit.

## 4. More permissive than ld.lld on a demoted section's own errors

ld.lld runs `shouldMerge` — and therefore its "size is not a multiple of
sh_entsize" and "writable SHF_MERGE section" errors — BEFORE it decides
whether to keep a section whole, so it errors even on a section it would then
demote. `elf_merge_build` checks those two only on the sections it actually
splits, so a malformed SHF_MERGE section that is also a relocation target is
demoted and links here while ld.lld refuses it.

Deliberate and recorded rather than changed: the difference only ever accepts
an input ld.lld rejects (never the reverse), the section is emitted verbatim,
and the errors that matter for a section we split are unchanged. Closing it is
a one-line reorder (run `elf_merge_reject` before `elf_merge_demote`) if strict
ld.lld-compatible diagnostics are ever wanted.
