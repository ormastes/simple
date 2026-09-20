# SMF wire relocation 4 (`GotRel32`) is applied with S = symbol address in both live loaders

**Date:** 2026-09-18
**Found by:** Fable, while writing the linker design
(`doc/05_design/compiler/linker/mold_mdsocpp_linker_design.md` §4).
**Status:** open. This is a **latent** defect: no reproducer has been run yet.

## Symptom (static analysis)

- **Where wire 4 comes from:** `80.driver/smf_elf_parser.spl:246` maps LLVM
  `R_X86_64_GOTPCREL` to SMF wire type 4 (`GotRel32`).
- **What that relocation means:** a GOTPCREL site holds the PC-relative offset of a
  GOT slot that contains the symbol's address. The instruction then **loads** through
  that slot (`mov sym@GOTPCREL(%rip), %reg`).
- **What the loaders do:** both live loaders (`99.loader/module_loader_compat.spl`,
  relocation types 1–5 at `:1324-1370`, and `os/smf/smf_dynlib.spl:759`) compute S as
  the symbol address itself.
- **Consequence:** without a GOT slot, the instruction loads the first 8 bytes of the
  symbol instead of its address.
- **Formula comment:** the header comment in `gpu_smf/smf_reloc_formulas.spl` claims
  the caller passes the GOT-entry address. No caller does.

## Fix direction

Either:
- make the SMF emitter relax GOTPCREL to PCREL for local definitions, rewriting
  `mov` into `lea` as lld does; or
- make the loader synthesize a per-module GOT.

Pin whichever rule is chosen with a golden in the relocation-oracle spec (linker plan,
lane A4a).
