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

## 5. Stricter than ld.lld for a named symbol past the end of a merged section

`elf_merge_piece_off` errors on `off > sh_size`. ld.lld errors there only for a
**section symbol plus addend** (`Symbols.cpp` `getSymVA`, guarded by
`if (d.isSection())`, which also returns 0 rather than an address at exactly
`offset == size`). For a **named** `Defined` symbol there is no diagnostic at
all: `SyntheticSections.cpp` `splitSections` pre-resolves it with

```
SectionPiece &piece = v >= ms->content().size() ? ms->pieces.back()
                                                : ms->getSectionPiece(v);
```

so any `v >= size` — including one *past* the end — is silently anchored on
the last piece. Measured with `.set strpast, abc+5` on a 4-byte
`.rodata.str1.1`: `ld.lld-23 -O1` links it and the program runs (exit 42),
while we fail with `offset 5 is outside merged section 4 (size 4)`.

**Kept deliberately.** Erroring is preferred to silently anchoring an
out-of-range label on the last piece: the address lld produces is not the one
the input asked for, and nothing tells the user. `off == size` is accepted (§1
of the C1 review), matching both lld paths for the legal one-past-the-end
label; only `off > size` diverges, and only by being louder. Reversing it, if
lld-identical behaviour is ever required, is a one-line clamp to the last
piece in `elf_merge_piece_off`.

## `--gc-sections`: `.eh_frame` is retained where lld collects (2026-09-19)

**We keep MORE than ld.lld does, deliberately.** This is a recorded divergence,
not a silent one.

`ld.lld` models `--gc-sections` liveness per FDE: it collects a function
section and drops that function's FDE from `.eh_frame` with it. This linker has
no per-FDE liveness, so until 2026-09-19 `elf_gc_reject` REFUSED any input
carrying `.eh_frame` — correct, but it made `--gc-sections` unusable on real
compiler output, and once `native_direct_platform_flags` was folded into the
internal route (which asks for `--gc-sections`) it blocked every internal link.

The fix is the safe SUBSET of lld's optimisation: `.eh_frame`, `.eh_frame.*`,
`.eh_frame_hdr` and `SHT_X86_64_UNWIND` are unconditional roots in
`elf_gc_is_root`. Being a root means their relocations are followed, so every
function an FDE describes stays live — which is the point: an FDE whose target
had been collected would carry a dangling pc-begin relocation. Retaining a
section lld would have dropped makes the image larger, never wrong.

### Read this before assuming `--gc-sections` removes dead CODE

**On real compiler output, code GC is effectively OFF. Only data is collected.**

`.eh_frame` is an unconditional root and a root's relocations are followed.
clang and gcc default to `-fasynchronous-unwind-tables`, so on this platform
EVERY function gets an FDE, and every FDE relocation points at its function's
section. Following them marks every function live. The result is correct and
safe — nothing that is reachable is dropped, and no FDE can dangle — but a
reader who sees "`--gc-sections` supported" and expects unreferenced functions
to disappear will be wrong. They do not. `.data.*`/`.rodata.*` sections that
nothing references ARE still collected, which is where the measured 4824 B ->
4424 B on the fixture comes from.

The fixture's `never_called_fn` survives for exactly this reason, and that is
the +32 B delta below — it is one instance of the general rule, not a corner
case. Recovering code GC needs real per-FDE liveness (parse `.eh_frame` CIEs
and FDEs, drop the FDEs of collected sections, then rebuild the section);
until then, treat `--gc-sections` on this engine as a data-only collector.

**Unexercised path:** the `SHT_X86_64_UNWIND` arm of `elf_gc_is_root` has no
coverage — this host is aarch64, where unwind data is the ordinary
`.eh_frame` section. It is there for x86_64 correctness and is untested.

Checked, not assumed: `.init_array`, `.fini_array`, `.preinit_array`,
`SHT_NOTE`, `SHF_GNU_RETAIN` and the `.init`/`.fini`/`.ctors`/`.dtors`/`.jcr`
families were ALREADY roots before this change, and `.gcc_except_table` is
reached through the `.eh_frame` relocations now that `.eh_frame` is live. None
of them was ever rejected for this reason.

**Not widened:** `SHT_GROUP` (COMDAT) and `SHF_LINK_ORDER` remain named
refusals. A spec asserts the reject strings for both are still present and that
the per-FDE one is gone.

### Measured delta vs `ld.lld --gc-sections`

Fixture `test/fixtures/linker/elf/gc_ehframe_a64.o` (`-O1 -fPIC -fexceptions
-ffunction-sections -fdata-sections`), one unreferenced `never_called_fn`,
aarch64 PIE, `-z now -z relro --gc-sections`, same CRT and `-lc`:

| section | ld.lld | internal:elf | delta |
|---|---|---|---|
| `.text` | 112 B | 128 B | **+16 B (+14.3%)** |
| `.eh_frame` | 104 B | 120 B | **+16 B** |

**+32 B total**, exactly `never_called_fn` and its FDE: the one section lld
collects and we retain. `nm` confirms it — absent from lld's output, present in
ours.

Whole-file size is NOT the divergence measure and points the other way (lld
4776 B vs internal 4424 B), because lld also emits `.eh_frame_hdr`, a build-id
note and `.hash`, none of which this engine produces
(`INTERNAL_ELF_UNPRODUCIBLE_FLAGS`, recorded separately).

GC still does real work with the root in place: the same object links to
4824 B with GC off and 4424 B with GC on, and runs (exit 42).
