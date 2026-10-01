# Hand-rolled module keys in 20.hir omit the tier elision the registry applies

- **Status:** 2 of 4 sites FIXED; 1 REAL-but-deliberately-unfixed; 1 benign
- **Filed:** 2026-09-01

## The defect class

The surface registry keys modules with `module_surface_canonical_module_name`
(`module_surface_source_identity.spl:11`, called from
`module_surface_registry.spl:79`), which strips `.spl`, `/`->`.`, a leading
`src.`, **all-digit tier segments**, and folds `std.` -> `lib.`.

Four sites in `20.hir` hand-roll only the FIRST THREE rewrites. Under
`SIMPLE_BOOTSTRAP` the module name is the raw physical path, so
`src/compiler/60.mir_opt/mir_opt/mod.spl` derives `compiler.60.mir_opt.mir_opt.mod`
while the surface is registered as `compiler.mir_opt.mir_opt.mod` -> exact miss.

Population is complete and was established by control query:
`grep -rn 'starts_with("src\.")' src/compiler/20.hir/` returns **6** hits — 2 are
the canonicalizers themselves, 4 are the hand-rolled sites.

## Site status

| site | verdict |
|---|---|
| `module_import_resolution.spl:252` | **FIXED** (PR #229) — was `missing importing module surface`, 78 files, 4796/5024 fatals |
| `module_import_registration.spl:804-838` | **FIXED** — the SILENT twin, see below |
| `module_import_resolution.spl:299-305` (`rel_base`) | **REAL, deliberately NOT fixed** — see below |
| `module_import_resolution.spl:381-385` (`self_name`) | benign — feeds only a literal skip; self-exclusion is caught by `sibling_canon == self_canon` |
| `hir_symbol_table_methods.spl:11-16` | benign — not registry-keyed; definer and lookup both read the same stored `defining_module`, so it is self-consistent either way |

### The silent twin (fixed)

`try_register_glob_reachable_symbol` probed the registry with the hand-rolled key
and, on a miss, returned `false` at the index guard **with no diagnostic**. The
glob re-export rescue was therefore never attempted for ANY numbered-path file,
and the unbound name surfaced later as a plain `unresolved name` with no hint
that a route existed. `module_surface_registry_index` is exact-match with no
canonical fallback (`module_surface_registry_index.spl:78-95`).

This is **not** bootstrap-only: it is called at `:534` BEFORE the
`ambient_bootstrap_enabled()` gate, from `types.spl:876` and
`_Expressions/expression_support.spl:410`.

Fix is additive (fallback-on-miss only, primary key untouched) and
mangling-safe: `derived_key` only locates the importer's own surface, while
emitted symbols use `surfaces[owner_index].module_name`.

### `rel_base` — real, and left alone on purpose

Same omission, and there is no second rescue: `:330` calls
`resolve_module_key(imp.module)` with the raw leading-dot spelling, which has no
relative handling (`registration:583-620`) and always misses. Reachable: 236
relative `use .` lines repo-wide (control: 34,922 total `use` lines), 89 under
`src/compiler/`, in 36 files across `99.loader`, `70.backend`, `40.mono` — all
numbered tiers.

**Not fixed because** `resolved_module_name` at this site is baked into emitted
call symbols (`:291-294`). Canonicalizing it risks converting a HIR-time
unresolved name into an lld undefined symbol — a primary-key change, not a
fallback. Needs its own change with link-level verification.

## Also found, not fixed

- `registration.spl:648` (`resolve_module_key_relative`) uses the
  non-canonicalizing `hir_module_logical_name_from_path` — a third instance of
  the same gap, on the re-export chase.
- `resolution.spl:330` calls `resolve_module_key`, not the `_relative` variant,
  on a leading-dot spelling — a missed reuse.
- `_hir_symbol_owner_module` strips only a LEADING `src/` while
  `module_logical_name_from_path` finds `src` anywhere; they diverge on absolute
  paths, and are paired at `module_reexport_materialization.spl:1118/1202`.

## Not established

- Whether `defining_module` is ever an absolute path (which would activate the
  `_hir_symbol_owner_module` divergence).
- Any empirical trace of `rel_base` misses: no stage-3 log carried one, and
  `bootstrap-progress.log` has 0 `import-miss` entries.
- The registration-site edit is **not syntax-verified by a linter** —
  `bin/simple lint` reports `unknown command` because the deployed binary is the
  bootstrap CLI. It is verified only by shape-matching an existing call and by
  the helper already being called at `:313` in the same file. The Stage-2
  build is the real check.
