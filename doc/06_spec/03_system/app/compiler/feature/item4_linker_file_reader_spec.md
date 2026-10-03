# Retained ELF record reading and section emission

Authority: `test/03_system/app/compiler/feature/item4_linker_file_reader_spec.spl`.
Requirements: ITEM4-REQ-004, 007, 009. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Open real ELF64 relocatable fixtures under explicit metadata/window quotas.
2. Read individual section, string, symbol and RELA records without materializing
   the complete object; compare against fixture bytes and record values.
3. Reject malformed table bounds, invalid string
   limits and record indices; synthesize NOBITS windows as zero bytes.
4. Interleave positional and sequential reads, proving positional operations
   preserve the retained cursor. Exercise replacement/truncation admission.
5. Emit section windows to an owned retained output; precheck total capacity,
   verify exact bytes and require cancellation to fail. Discard partial output.

The caller owns publication and cleanup. This reader/emitter does not perform
full symbol resolution, final layout, streamed relocation or memory certification.
# Owner API correction (2026-10-03)

The executable spec now holds named `var` owners. Sequential IO uses retained
`read`/`write`/`close` mutating methods; section copying is
`output.elf_file_copy_section_v1(object, index, cancelled)` and view closure is
`object.elf_file_close_v1()`. Cursor checks after successful and cancelled copies
inspect the same output owner. This corrects value-semantics writeback, with
runtime evidence still UNRUN.
