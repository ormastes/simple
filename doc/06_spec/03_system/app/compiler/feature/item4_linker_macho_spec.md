# Freestanding Mach-O images

Authority: `test/03_system/app/compiler/feature/item4_linker_macho_spec.spl`.
Requirements: ITEM4-REQ-003, 004, 006, 007. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Load real LLVM x86-64 and ARM64 objects and archive providers.
2. Construct static MH_EXECUTE images and inspect segment permissions, thread
   entry state, relocation bytes and deterministic output.
3. Exercise transitive archive extraction, strong/weak selection and common
   storage using real symbols and references.
4. Mutate symbol indices, patch ranges, metadata command lengths and section
   addresses; require named rejection rather than a malformed image.
5. Mutate a real ARM64 ADD instruction to SUB or reserved PAGEOFF12 forms;
   require rejection while the original ADD fixture remains accepted.
6. Reject unsupported TLS/dyld inputs and an insufficient output-size limit.

These are image-construction assertions. No Darwin execution, signing, dyld,
TLS or unwind qualification follows from them.

