# Internal ELF linker concatenates `.note.gnu.property` instead of merging (2026-09-19)

**Status:** open. **Found by:** lane C2 (x86_64 dynamic execution proof).
**Where:** `src/compiler/70.backend/linker/elf/elf_static_link.spl`. `elf_out_name` sends
every SHT_NOTE input to an output section with the same name, and
`elf_static_contents` appends the inputs one after another.

## Observed

The internal engine links x86_64 glibc hello: Ubuntu noble `crt1.o`, `crti.o`, `crtn.o`, and
`hello_libc_x64.o` (clang, no `-fcf-protection`). The output's `.note.gnu.property` holds
three `NT_GNU_PROPERTY_TYPE_0` notes:

```
x86 feature: IBT, SHSTK, x86 ISA needed: x86-64-baseline
x86 feature: IBT, SHSTK
x86 feature: IBT, SHSTK
```

`ld.lld-23` links the same inputs with no `.note.gnu.property` at all. It ANDs
`GNU_PROPERTY_X86_FEATURE_1_AND` across all inputs, the hello object has no
note, so the result is 0 and the section is dropped.

## Impact

The output claims IBT/SHSTK for code that was not built for them. The gABI
allows only one property note. The engine emits no `PT_GNU_PROPERTY`, so the
kernel and ld.so ignore the section today and both outputs run (exit 42). Any
tool that reads the section does get wrong information.

## Fix direction

Merge the notes in the way ld.lld does. AND `FEATURE_1_AND`, x86_64 and aarch64, treating a
missing note as 0. Emit one note plus `PT_GNU_PROPERTY` when the result is
non-zero, and emit no section when it is 0. Until the merge exists, reject a
link where the AND is non-zero, naming the reason, and drop the notes when it
is zero.
