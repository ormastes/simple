# spipe-docgen: stale syntax detection renders modern SSpec specs as 100% stubs

- **Date:** 2026-07-19
- **Status:** fixed
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

## Resolution 2026-08-17 — FIXED

Root cause: spipe-docgen recognised only the LEGACY bare spec syntax
(`it "name":`, `describe "name":`) — the `trimmed.starts_with("it ") and
trimmed.contains("\"")` shape — at 18 sites across
`src/app/spipe_docgen/spipe_docgen/{parser,generator}.spl`, including
`validate_spec` (parser.spl:367) and `is_scenario_line` (parser.spl:989).
Modern manual-first specs use the CALL form `it("name"):` / `describe("name"):`,
which has no space after the keyword, so every such spec counted zero scenarios
and rendered as a stub.

Fix: one shared predicate `spec_kw_line(trimmed, kw)` added to
`src/app/spipe_docgen/spipe_docgen/common.spl`, accepting both `kw + " "` and
`kw + "("`. All 18 sites in `parser.spl` and `generator.spl` now route through it
(scenario counting, scenario lists, slow/skip/pending classification, describe
detection, manual rendering), so the two spellings can never drift apart again.

Evidence (seed `bin/simple`, 2026-08-17):
- `test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl`
  -> `3 examples, 0 failures` x2 blocks, rc=0.
- Ablation (drop the call-form arm): same spec RED — `✗ counts modern call-form
  scenarios`, `✗ recognises the modern call form`. Restored -> GREEN.
- `test/01_unit/app/tooling/spipe_docgen_modern_spec_family_scan_spec.spl` sweeps
  real call-form specs under `src/lib/hardware/nand_emu/test` -> `2 examples, 0 failures`.
- No regression: `test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl` is
  `61 examples, 16 failures` both BEFORE and AFTER the change, byte-identical
  failure set (pre-existing, unrelated).

Specs added:
- `test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl` (reproducing)
- `test/01_unit/app/tooling/spipe_docgen_modern_spec_family_scan_spec.spl` (class detection)

Status: fixed.
