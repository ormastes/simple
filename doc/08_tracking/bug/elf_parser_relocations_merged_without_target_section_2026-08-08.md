# `ElfObject.relocations` merges every SHT_RELA section without recording its target section

- Status: RESOLVED 2026-08-17 (fix + reproducing spec + class-detection spec landed).
- Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Resolution (2026-08-17)

Root cause, precisely: `ElfSectionHeader`
(`src/compiler/70.backend/linker/elf_inspect.spl:56-63`) had **no `sh_info`
field at all**. Both section-header readers — `elf_parse_sections`
(`elf_inspect.spl:171-190`) and the richer one inside `elf_parse_object`
(`elf_parser.spl:331-351`) — therefore skipped ELF64 shdr offset 44 entirely.
An earlier partial fix had added `ElfRelocation.section_idx` (which RELA
section an entry came from), but with `sh_info` unparsed that index could not
be resolved to a target, so the information was still unrecoverable.

Fix:
- Parse `sh_info` (offset 44, u32) in **both** readers.
- Add `ElfSectionHeader.sh_info`.
- Add `ElfRelocation.target_section_idx`, populated from the owning RELA
  section's `sh_info` in `elf_parse_relocations`
  (`src/compiler/70.backend/linker/elf_parser.spl:259-265`).

This is exactly step 1 of the "Unblock condition" below. Step 2 (consumers
keying off the field) still applies to whoever adds the first consumer.

Specs:
- `test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl`
  (reproducing) — a synthetic object with two RELA sections, `sh_info` 1 and 2.
- `test/01_unit/compiler/backend/linker/elf_section_header_field_parity_spec.spl`
  (class detection) — every section-header field cross-checked against an
  independent raw-byte re-read, through BOTH readers.

Evidence, fix reverted to `val sh_info = 0`:

    reproducer      Results: 4 total, 2 passed, 2 failed
    detection spec  Results: 4 total, 0 passed, 4 failed

The detection spec caught strictly more than the reproducer, including the
`elf_inspect.elf_parse_sections` reader that the reproducer never exercises.

Evidence, fix in place:

    elf_reloc_target_section_spec.spl          Results: 4 total, 4 passed, 0 failed
    elf_section_header_field_parity_spec.spl   Results: 4 total, 4 passed, 0 failed
    elf_parser_spec.spl (pre-existing)         Results: 16 total, 16 passed, 0 failed

- Severity: LOW (latent — no production consumer reads `ElfObject.relocations` today)
- Found: adversarial review of ELF/linker code, 2026-08-08, alongside two related
  MEDIUM defects in `src/compiler/80.driver/smf_elf_parser.spl` (see
  `_find_text_section_index` bounds-guard fix and the `-ffunction-sections`
  multi-`.text*` merge fix, same date, same review).

## Location

`src/compiler/70.backend/linker/elf_parser.spl:375-383`, inside
`elf_parse_object` (or equivalent object-parsing entry point that builds an
`ElfObject`):

```
# Find and parse first RELA section
var relocations: [ElfRelocation] = []
for sec in sections:
    if sec.sh_type == SHT_RELA:
        val rela_relocs = elf_parse_relocations(bytes, sec)
        var k: i64 = 0
        while k < rela_relocs.len():
            relocations = relocations.push(rela_relocs[k])
            k = k + 1
```

`ElfRelocation` (line 64-68) carries only `r_offset`, `r_info`, `r_addend` —
no field recording which section the entry relocates (i.e. no `sh_info` of
the owning `SHT_RELA` section). Under `-ffunction-sections`, an object can
have many `SHT_RELA` sections (`.rela.text.foo`, `.rela.text.bar`, ...), each
one's `sh_info` naming a *different* target section. This code concatenates
every one of them into a single flat `relocations` list with no way to tell,
after the fact, which relocation belongs to which section. `r_offset` values
are section-relative, so applying any of these relocations requires knowing
the target section — that information is discarded here.

This is exactly the class of defect fixed the same day in the sibling file
`src/compiler/80.driver/smf_elf_parser.spl`'s `extract_elf_relocations`,
which explicitly matches each `SHT_RELA` section's `sh_info` to the code
section(s) it belongs to and rebases offsets accordingly (see that file's
`_find_text_section_indices` / `extract_elf_relocations`). This file does not
do the analogous thing.

## Why not fixed now

Verified via `grep -rn '\.relocations\b'` (anchored against a `.spl` grep of
`src/compiler/70.backend/linker/*.spl` and the broader `src/compiler` tree)
that no current caller reads `ElfObject.relocations` off an object parsed by
this function — it is dead weight today, not a live silent-corruption path.
Fixing it correctly means widening `ElfRelocation` with a target-section
field (or index) and updating every call site that constructs/consumes one,
which is out of scope for the two live MEDIUM defects this review was
scoped to fix. Left as latent per review instructions ("no production
consumer today ... file if you don't fix").

## Unblock condition / suggested fix

When a consumer of `ElfObject.relocations` is added:
1. Add a `target_section_idx: i64` (or equivalent) field to `ElfRelocation`,
   populated from the owning `SHT_RELA` section's `sh_info`.
2. Any code applying these relocations must key off that field to know which
   section's bytes to patch — do not assume all relocations target one
   section, and do not assume they're contiguous per section in the merged
   list (they are grouped by section-loop order today, but that's incidental,
   not a documented invariant).
