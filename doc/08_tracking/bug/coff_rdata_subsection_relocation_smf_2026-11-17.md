# Seed `compile` rejects COFF `.rdata$<sub>` sections that carry relocations

- **Status:** verification-pending
- **Found:** 2026-11-17, Windows host, seed `C:/dev/wt/seed-20261117c/simple.exe`
- **Repro:** `simple.exe compile src/lib/nogc_sync_mut/io/disk_admission.spl -o x.o` ->
  `codegen: Failed to preserve SMF imports/relocations from object code: Invalid data: Failed to parse object file: Invalid section: relocation source section .rdata$subsection is not executable code`

## Cause
`ParsedObject::parse` (`src/compiler_rust/compiler/src/linker/object_parser.rs`) only
represents relocations inside the flattened SMF code buffer. A COFF read-only data
section holding a pointer table (DIR64 relocation) had no representable home.

## Fix
Read-only data sections that carry relocations are laid into the code buffer
(`SectionType::Code`, READ-only flags), aligned by padding the previous code
section. Ordinary code sections keep the existing as-is concatenation.

## Tests
`linker::object_parser::tests::coff_rdata_subsection_with_relocation_is_laid_into_code_buffer`;
`cargo test -p simple-compiler --lib linker::` 160 passed; `--lib smf` 12 passed.

## Remaining
End-to-end re-run of the repro command on a seed rebuilt with the fix.
