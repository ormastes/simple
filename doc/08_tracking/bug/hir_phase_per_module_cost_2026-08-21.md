# HIR phase costs ~20x parse per module (full-registry rescans) — 2026-08-21

## Status
RESOLVED 2026-08-21 — a865dced154 memoizes frozen-registry owner scans in the package-dep and bootstrap-global resolvers. Evidence: per-module HIR lowering 0.28s -> 0.15s (61-module fixture), per commit message and hir_package_dependency_scan_memo_spec.spl.


## Symptom
Stage1 bootstrap (self-hosted `src/compiler` interpreted by the Rust seed):
parse finished 662 modules in ~50 min (~5 s/module); the HIR phase
(`[build] hir N/662`, step 2/6) managed 33 modules in ~55 min (~100 s/module)
in run1 — HIR alone extrapolates to ~18 h.

## Mechanism (defect, not inherent cost)
Two HIR resolvers scan the ENTIRE frozen module-surface registry (662 surfaces)
with no early exit — they must prove the owner is UNIQUE — and both are invoked
per consumer rather than per answer. The registry is frozen for the whole HIR
phase, so every one of those scans recomputes a constant.

1. `_Items/module_reexport_materialization.spl`
   `materialize_imported_field_package_dependency`: full `surfaces` sweep per
   unresolved composite-FIELD dependency, calling `module_surface_package_name`
   (canonicalize + `split(".")` + slice + `join(".")`, i.e. a heap allocation)
   and `hir_module_declares_item` (6 dict probes) per candidate.
   Cost: O(modules x registry x field-deps) with per-candidate allocation.
2. `_Items/module_import_registration.spl`
   `try_register_bootstrap_global_symbol`: same full sweep, but invoked LAZILY
   from BODY lowering for every UNBOUND NAME (see the BGS1 note there).
   Cost: O(bodies x names x registry).

Neither depends on the module's own size, which is why HIR — not parse — is the
phase that blows up as the closure grows.

## Fix
Memoize both, since the registry is immutable for the phase:
- `field_package_dep_memo` keyed by (declaring module, dependency) -> surface
  index, `-1` for none/ambiguous (both were already no-ops).
- `bootstrap_global_owner_memo` keyed by name -> owning surface index.
- `surface_package_name_memo` (per surface module name) removes the split/join
  allocation from the inner loop.
Two observable scan counters (`field_package_dep_scan_count`,
`bootstrap_global_scan_count`) make the mechanism testable rather than only
timeable. Semantics unchanged: the ambiguity early-return is preserved as a
memoized `-1`.

## Measurement
Fixture: 61-module single-package closure whose composites carry field types
declared by a package SIBLING with no import edge (exactly the shape that drives
resolver 1), built with the same seed and driver as the bootstrap, `--threads 1`.
Wall time of the `[build] hir` span, from per-line timestamps:

| | HIR span (61 modules) | per module |
|---|---|---|
| pre  | 17 s | 0.28 s |
| post |  9 s | 0.15 s |

1.9x on a 61-surface registry. The eliminated term is linear in registry size,
so the bootstrap's 662-surface registry is ~11x further from the memo-hit path
than this fixture. Diagnostics are byte-identical pre/post (same 123,681-byte
stderr, only the pid in the temp-file name differs), so no error changed.

## Pin
`test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl` asserts
the scan COUNT, not a wall clock: repeated identical queries scan once, a
different dependency name scans again, and a surface's package name is computed
once. It pins the algorithm, so it cannot pass on the pre-fix code (the counters
did not exist) and cannot be satisfied by a faster machine.

## Follow-up landed the same day: inverted indices (2026-08-21, second commit)
The memos above still answered each question with a full-registry sweep the
FIRST time, and a third resolver had no memo at all. All three now read an index
built once per lowerer from the frozen registry:

- `surface_decl_owners` (`{name: [surface_index]}`, built in
  `_Items/module_lowering.spl`) replaces the sweeps in
  `try_register_bootstrap_global_symbol` (a non-singleton owner list is exactly
  the old "ambiguous -> give up") and in
  `materialize_imported_field_package_dependency`, whose candidate loop now runs
  over the one or two surfaces that declare the name at all. The
  `bootstrap_global_owner_memo` added by the first commit is therefore gone —
  the index subsumes it.
- `package_sibling_names` / `package_sibling_canons` (canonical package ->
  member modules) replace the per-module sweep over every registry KEY in
  `resolve_package_sibling_symbols`
  (`_Items/module_import_resolution.spl`), which canonicalized each key with a
  split/join and deduplicated into a fresh dict on every module lowered. The
  dedup by canonical name now happens once, during the index build.

Measured on a 240-module package fixture of the same shape, `--threads 1`,
`[build] hir` span:

| | HIR span (240 modules) | per module |
|---|---|---|
| memos only (a865dced154) | 54 s | 0.225 s |
| + inverted indices | **32 s** | **0.133 s** |

Per-module cost is now flat between the 61- and 240-module fixtures (0.15 s vs
0.13 s), which is the property that was missing: the eliminated terms were all
linear in registry size, so they grew with the closure rather than with the
module. Diagnostics are unchanged (same stderr content on the 61-module fixture;
only blank-line wrapping of the truncation banner differs).

Pin: two further examples in the same spec assert that the declaration-owner
index and the package-sibling index are each built exactly ONCE no matter how
many distinct names or packages are queried.

## Third commit: registry KEY lookup was also linear
`hir_module_surface_index` (`_Items/module_lowering.spl:131`) compared every
registry key in `ordered_names` (~2 per module, ~1300 in a full bootstrap) to
resolve ONE name, and is called per import, per package sibling and per
re-export hop. Replaced at the five in-lowerer call sites by
`surface_index_for_name`, a dict probe over an index built once from the same
aligned arrays (values are i64, so the ModuleSurface-payload hazard documented
on the linear form does not apply). First-alias-wins and the out-of-range
bounds check are preserved exactly.

240-module fixture, `[build] hir` span: 32 s -> **27 s** (0.133 -> 0.113 s per
module). Cumulative for the day on that fixture: 54 s -> 27 s, 2.0x, with the
per-module cost now flat in registry size. Diagnostics unchanged.

## Not fixed here
`hir_module_declares_item` is still a linear probe of six dicts when called
directly (the index calls it implicitly, once per surface, at build time), and
the surface registry itself is still rebuilt per lowerer rather than shared
across phases. Neither is multiplicative any more.
