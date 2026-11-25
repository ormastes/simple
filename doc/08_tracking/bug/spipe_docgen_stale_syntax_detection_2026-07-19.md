# spipe-docgen: stale syntax detection renders modern SSpec specs as 100% stubs

- **Date:** 2026-07-19
- **Status:** RESOLVED 2026-11-25 (see "Resolution 2026-11-25" below)
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

## Resolution 2026-11-25 (work/p2w5-ac-20261125)

Root cause 2 (inline `"""` docstrings) had already been fixed — the scanner at
`parser.spl` accepts the column-0 inline opener (`doc_open_inline`). Root cause
1 was still live: every scenario detector recognized only the legacy
`it "Name":` form. Fixed all six sites in
`src/app/spipe_docgen/spipe_docgen/parser.spl` to also accept the call form:

- `validate_spec` scenario count: `starts_with("it \"")` → also `starts_with("it(")`
- `is_scenario_line`: added `it(`, `slow_it(`, `pending(`, `skip_it(` variants
- `extract_test_structure_with_default` rendering branches for
  `skip_it`/`pending`/`slow_it`/`it`: added the matching paren forms

The secondary path-mirroring item (`normalize_spec_relative_path` flattening
`src/.../test/x_spec.spl` to a basename) is unchanged and remains a separate,
cosmetic issue.

Evidence (Rust seed v1.0.0-rc.1, Windows host, `SIMPLE_LIB=src bin/simple.exe
run`, hybrid mode; a package-local probe driving the real
`app.spipe_docgen.parser` functions, deleted after use):

- BEFORE: `is_scenario_line("it(\"does x\"):")` = false,
  `is_scenario_line("slow_it(\"does x\"):")` = false,
  `is_scenario_line("it \"does x\":")` = true.
- AFTER: both modern forms = true, legacy form still true,
  `is_scenario_line("val it = 3")` still false;
  `validate_spec` on a doc-block-less source with two `it("..."):` scenarios
  now reports `docs_present=true`, `doc_lines=20`;
  `extract_test_structure` renders the modern scenario title.

Verification limit: the repo-wide spec harness and the `spipe-docgen` CLI
delegation both fail at HEAD with `unknown decorator
'@representation_boundary'` (seed/HEAD source-binary inconsistency), so the
pre-existing reproducing spec
`test/01_unit/app/tooling/spipe_docgen_modern_it_scenario_count_spec.spl`
(which pins exactly this contract) could not be executed; the probe above
exercises the same functions and assertions directly.
