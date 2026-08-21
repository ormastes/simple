# HIR phase costs ~20x parse per module (full-registry rescans) — 2026-08-21

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

## Not fixed here
`_Items/module_import_resolution.spl:370` (package-sibling fallback) still
sweeps `ordered_names` once per module lowered with per-key canonicalization,
and `hir_module_declares_item` still has no inverted `name -> [surface_index]`
index. Both are follow-ups; the two memos above remove the multiplicative terms.
