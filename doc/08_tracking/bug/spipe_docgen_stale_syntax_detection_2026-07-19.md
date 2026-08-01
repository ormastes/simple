# spipe-docgen: stale syntax detection renders modern SSpec specs as 100% stubs

- **Date:** 2026-07-19
- **Status:** open
- **Severity:** medium (docgen unusable for current-convention specs; manual-first
  authoring investment invisible in generated manuals)
- **Area:** src/app/spipe_docgen

## Symptom

`bin/simple spipe-docgen <spec> --output doc/06_spec --no-index` on specs that
follow the mandated manual-first convention (outcome-named `it("...")`, inline
`"""docstrings"""`, `step()` calls) reports
`Complete documentation: 0/N, Stubs: N/N (100%)` and collapses every
`describe()` into one `AUTO <basename>` placeholder entry.

Reproduced on `src/lib/hardware/nand_emu/test/scenario_spec.spl` (8 scenarios →
1 stub) and `chip_spec.spl` (16 → 1 stub), 2026-07-19 seed. Pre-existing
generated docs (e.g. `doc/06_spec/01_unit/os/riscv_fpga_linux_spec.md`) show the
identical stub shape — systemic, not spec-specific.

## Root causes (source-confirmed)

1. `src/app/spipe_docgen/spipe_docgen/parser.spl:364` — `validate_spec`
   counts scenarios only via `trimmed.starts_with("it \"")` (legacy `it "Name":`
   form). The codebase uses `it("Name"):` exclusively → `scenario_count == 0`.
2. `parser.spl:93` — the doc-block scanner recognizes only a standalone `"""`
   line as delimiter; the mandated inline `"""text...` opening (docstring
   attached per-`it`) is never matched → `doc_blocks.len() == 0`.
3. Net: `docs_present=false` → whole-file AUTO/stub fallback regardless of real
   docstring content.

## Secondary

`generator.spl:53-55` `normalize_spec_relative_path` splits on `/test/` and
keeps only the basename — `src/lib/hardware/nand_emu/test/x_spec.spl` lands
flat at `doc/06_spec/x_spec.md` instead of mirroring the source path.

## Expected

Docgen recognizes the current-convention syntax (`it("Name"):`, inline
docstrings) and mirrors source paths under doc/06_spec. The two 100%-stub
outputs generated during diagnosis were deleted rather than committed.
