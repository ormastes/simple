# SMF ELF: code/reloc section selection still diverges on truncated objects, and `-ffunction-sections` is made consistent rather than correct

- **Status:** OPEN
- **Found:** 2026-08-08, adversarial review of `f13a082b3823` + `381cd611097f`
- **File:** `src/compiler/80.driver/smf_elf_parser.spl`

Both commits are sound. The `.rela` 5-byte prefix test really did accept
`.rela.rodata` / `.rela.data.rel.ro` / `.rela.eh_frame`, and selecting the
relocation section by `sh_info` really is the correct ELF-defined way to pair it
with the code section. Confirmed against the ELF64 layout: `sh_info` sits at
byte 44 of a section header, `SHT_RELA` is 4, and `_find_text_section_index()`
can never return 0 (index 0 is always `SHT_NULL`), so the `sh_info == text_idx`
comparison cannot be satisfied by an unrelated `sh_info` of 0. Two gaps remain.

## 1. The two selection rules still diverge on a truncated object (MEDIUM)

The comment at `smf_elf_parser.spl:25-28` states the invariant:

> Keep this in step with `extract_code_from_object` — `extract_elf_relocations()`
> relies on the two agreeing.

They agree on the *predicate* (first `SHT_PROGBITS` whose name starts `.text`)
but not on what happens when the section's bytes are out of range:

- `extract_code_from_object` (line 124) checks `end_off <= object_code.len()`
  and, when that fails, **falls through to `i = i + 1` and keeps searching** —
  so it may return a *later* `.text*` section, or drop out of the loop and
  return the whole raw object.
- `_find_text_section_index` has no such check and **returns the first match
  immediately**.

On any object whose first `.text*` section header points past the end of the
buffer — truncated file, short read, a hand-built or corrupt object — the index
names section *N* while the bytes come from section *M* (or from the raw-bytes
fallback). That is precisely the code/reloc mis-pairing class `381cd611097f`
set out to eliminate, reintroduced through the malformed-input path.

Suggested fix: give `_find_text_section_index` the same `sh_offset + sh_size <=
object_code.len()` guard, so a section that `extract_code_from_object` skips is
skipped here too.

## 2. `-ffunction-sections` is made *consistent*, not *correct* (MEDIUM)

The commit message and the in-code comment both frame `-ffunction-sections` as
handled. What the fix actually guarantees is that the relocations returned
belong to the code bytes returned. Under `-ffunction-sections` there are *N*
`.text.<fn>` sections, and:

- `extract_code_from_object` returns the bytes of the **first one only**;
- `extract_elf_relocations` returns the relocations of that same first one.

Every other function's bytes and relocations are silently dropped. The SMF
module built by `build_smf_with_relocations` (`smf_writer.spl:556`) therefore
contains one function out of *N*, with no diagnostic. That is a strict
improvement over applying function *b*'s offsets to function *a*'s bytes —
wrong output became truncated output — but a caller compiling with
`-ffunction-sections` still gets a broken module, and the code comment reads as
if the case were resolved.

The real fix is to concatenate all `.text*` PROGBITS sections and rebase each
`SHT_RELA` section's `r_offset` by its target section's offset within the
concatenation. Until that lands, the honest interim step is to *detect* the
condition (more than one `.text*` PROGBITS section) and fail loudly rather than
emit a silently truncated module.

## 3. The same defect class is UNFIXED, and worse, in the linker's own ELF parser (LATENT — no production consumer today)

`f13a082b3823` / `381cd611097f` fixed `80.driver/smf_elf_parser.spl`. The family
was not swept: `src/compiler/70.backend/linker/elf_parser.spl:375-383` has the
same bug in a stronger form.

```
# Find and parse first RELA section
var relocations: [ElfRelocation] = []
for sec in sections:
    if sec.sh_type == SHT_RELA:
        val rela_relocs = elf_parse_relocations(bytes, sec)
        ... relocations = relocations.push(rela_relocs[k])
```

The comment says "first RELA section"; the code accumulates **every** one —
`.rela.text`, `.rela.rodata`, `.rela.eh_frame`, `.rela.data.rel.ro` — into a
single flat list. And `ElfRelocation` (line 64) carries only
`r_offset` / `r_info` / `r_addend`, with **no field naming the section the entry
applies to**, so the information needed to separate them is destroyed at parse
time and cannot be recovered downstream.

Since `r_offset` is section-relative, the resulting list is not merely
mis-ordered, it is incoherent: a `.rela.rodata` entry with `r_offset` 0x10 is
indistinguishable from a `.rela.text` entry with `r_offset` 0x10. Any consumer
applying these against extracted `.text` bytes patches the wrong bytes. This is
the identical failure `381cd611097f` describes ("the loader applies at the wrong
offsets in the wrong function"), one directory over, still live.

Minimum fix: add a target-section field to `ElfRelocation` (populate from the
RELA section's `sh_info`) and have consumers filter on it — the same `sh_info`
mechanism `381cd611097f` adopted.

**Severity qualification.** Rated LATENT rather than HIGH because no production
code reads the merged list today: grepping `elf_parse_object` finds only
re-exports, three "round-trips through elf_parse_object" comments, and the
`_spec.spl` files under `test/01_unit/compiler/backend/linker/`. Nothing in
`src/` consumes `ElfObject.relocations`. It becomes HIGH the moment a caller
does, and the parse-time information loss means such a caller has no way to
discover the problem — which is why it is worth fixing before that caller
exists rather than after.

### Related trap in the same file

`ElfSectionHeader.sh_addr` has two contradictory meanings depending on which
producer built it: `elf_parser.spl:344` stores the **file offset** in it
(`sh_addr: sh_off,   # repurposed: file offset for elf_parser purposes`), while
`elf_inspect.spl:184` stores the real **virtual address**. `elf_parse_relocations`
(line 239) reads `rela_section.sh_addr` as a file offset, so passing it a header
built by `elf_inspect` reads relocations from the wrong place — and for a
relocatable object `sh_addr` is 0, i.e. it would read from the ELF magic.

## Also noted

`SHT_REL` (type 9, implicit-addend relocations) is not handled — only
`SHT_RELA` (4). Not a regression, and x86_64 objects use RELA, but a 32-bit or
ARM object would yield zero relocations with no diagnostic.
