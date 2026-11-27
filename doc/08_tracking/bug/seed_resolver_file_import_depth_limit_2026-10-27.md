# Seed resolver: file imports deeper than 6 path segments resolve as items

- **Status:** open. **Owner:** Rust seed module resolver (src/compiler_rust module loader).
- **Symptom:** `use a.b.c.d.e.f.g.File.{T}` with 7+ segments is not resolved to `File.spl`. The last segment is treated as an item of the directory module, which fails with `Module "..." does not export 'File'`.
- **Evidence:** this was probed while fixing `mdsoc_entity_view_pascalcase_file_import_unresolvable_2026-10-26.md`. `compiler.mdsoc.transform.feature.ev3.hir_view` (6 segments) resolves; `...feature.hir_to_mir.ev4.hir_view` (7 segments) does not. Case of the file name makes no difference.
- **Workaround in use:** the `entity_view/__init__.spl` files re-export with `export use .<file>.{T}`, and the specs import from the package.
- **Repro:** move a probe file to depth 7 under src/compiler and import it from a spec with `bin/simple.exe test`.
