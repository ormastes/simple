# Seed: SPL-PAT-001 location names the importing file, not the defining file

- id: seed_spl_pat_001_location_names_importer_file_2026-11-13
- status: open
- severity: P3 (diagnostic quality)
- found: 2026-11-13, lane work/option-pattern-shape-20261113

## Symptom

When the offending pattern is in an imported module, the seed's
`DiagLocation.render` prints the ROOT file with the imported file's line/column,
e.g. `src/app/mcpgdb/main.spl:67:9 (fn extract_string_field_with_pattern)` for a
site that is really `src/app/mcpgdb/json_helpers.spl:67`. Only the `(fn ...)`
name is reliable.

## Cause

`hir/lower/import_loader.rs` deliberately keeps `current_file` at the caller
while imported bodies are lowered; `option_pattern_shape_diag.rs` reads
`self.current_file`.

## Fix direction

Carry the defining module path on the lowered function (or swap
`current_file` around imported-body lowering) and render that.
