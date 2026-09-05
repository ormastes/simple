# `hardware.rv32imac.*` modules gone; 6 specs orphaned (2026-08-18)

## Status
OPEN — reported, NOT fixed. Deleting the specs needs approval.

## Symptom
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_decode
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_regfile.Rv32RegFile
    error: semantic: Cannot resolve module: hardware.rv32imac.ext.rv32_muldiv.muldiv_execute
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_execute.alu_execute
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_compressed
    error: semantic: Cannot resolve module: hardware.rv32imac.core.rv32_pipeline_ctrl

Affected specs (all under `test/01_unit/hardware/rv32imac/`):
`rv32_alu_spec.spl`, `rv32_compressed_spec.spl`, `rv32_decode_spec.spl`,
`rv32_muldiv_spec.spl`, `rv32_pipeline_spec.spl`, `rv32_regfile_spec.spl`.

## Finding
There is no `src/lib/hardware/rv32imac/` tree and no retarget exists. The
surviving `src/lib/hardware/rv32gc/` holds only `top/rv32_machine.spl`; the
symbols the specs import are absent tree-wide:

    /usr/bin/grep -rn "fn decode_opcode|Rv32RegFile|fn is_compressed|fn decompress_rvc|fn alu_execute" src/lib/hardware/
    (only hit: rv64gc_rtl/mul_div.spl:373 fn muldiv_execute — rv64, different signature)

`src/lib/hardware/rv32i_rtl/` is a differently-shaped RTL library
(`decode.spl`, `regfile.spl`, `m_extension.spl`) with a different API, not a
rename of these modules. The same shape applies to the sibling
`hardware.rv64gc.*` / `hardware.riscv_common.pkg.*` unresolved imports in the
same shard logs.

## Required decision
Either the rv32imac RTL model is restored, or these 6 specs are retired. Both
need owner approval; this lane did neither.

## History answer (2026-08-18)

The modules were **implemented, then lost in a history divergence** — they were
neither deliberately deleted on the current lineage nor written-spec-ahead-of-code.

Evidence:

- The specs import `hardware.rv32imac.*`, which resolved to **`src/hardware/rv32imac/`**
  (NOT `src/lib/hardware/`, which is why the earlier tree-wide grep of
  `src/lib/hardware/` found nothing — the search was scoped to the wrong root).
- Added by `3e1c86706a7` (2026-03-15) *"feat: add VHDL emulation environment and
  RV32IMAC processor"*: **26 `.spl` files**, ~3,500 lines, including every symbol
  the orphaned specs import —
  `core/rv32_decode.spl` (`decode_opcode`, `decode_rd`, `decode_rs1`, `decode_imm_i`),
  `core/rv32_regfile.spl` (`Rv32RegFile`), `core/rv32_compressed.spl` (`is_compressed`,
  `decompress_rvc`, `rvc_reg`), `core/rv32_execute.spl` (`alu_execute`),
  `ext/rv32_muldiv.spl` (`muldiv_execute`), `core/rv32_pipeline_ctrl.spl`,
  `pkg/rv32_{isa,types,config,debug}_pkg.spl`, plus `debug/`, `mem/`, `periph/`, `top/`.
- **`3e1c86706a7` is NOT an ancestor of current `HEAD`** (`git merge-base --is-ancestor`
  → exit 1). The only ref containing it is the tag **`refs/tags/v0.9.1`**.
- There is **no deletion commit**: `git log --all --diff-filter=D -- 'src/hardware/rv32imac/**'`
  returns nothing, and the path is absent from the last 4,000 commits of `HEAD`
  ancestry. Today `src/hardware/` contains only `fpga_linux/`.
- The specs themselves entered the current lineage via `ae55a746719`
  *"fix(vcs): restore tree wiped by 6f86ff32a7d"* — i.e. the wipe-restore carried
  the `test/` half forward but not the `src/hardware/rv32imac/` half.

So this is the same silent-loss class as the other REBASE91/tree-wipe residue: a
whole implementation subtree present at `v0.9.1` never made it onto the rewritten
mainline, while its specs did.

## Recommendation

**Restore, do not retire.** The content is not lost — it is fully recoverable:

    git checkout v0.9.1 -- src/hardware/rv32imac/     # 26 files (verify tree first)

Restoration is preferable to retiring 6 specs because (a) the code exists and was
once green, (b) retiring specs for code that a wipe dropped would make the loss
permanent and invisible, and (c) the specs are the only remaining record of the
module's contract. The restore should be a separate, owner-approved change: it
re-adds a `src/hardware/` product subtree, must be re-validated against the current
compiler (the code is from 2026-03-15 and predates later grammar/stdlib changes),
and may need import-path updates if `src/hardware/` is no longer a resolution root.

Until then the 6 specs stay in place, unmodified. **Do not delete them.**
