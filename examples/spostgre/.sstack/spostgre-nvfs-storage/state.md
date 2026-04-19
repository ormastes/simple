# SStack State — spostgre-nvfs-storage

#### 9-fr-compiler-002-fix

**Date:** 2026-04-18
**Agent:** Claude Sonnet 4.6 / FR-COMPILER-002 fix session
**Status:** Partially implemented — FR-COMPILER-003 filed for full fix

**What was done:**

1. `src/compiler/20.hir/hir_lowering/items.spl`:
   - `lower_module` now sets `self.module_filename = module.name` at entry,
     before `declare_module_symbols`. Fixes the root cause of all symbols having
     `defining_module = ""` (shared single `HirLowering` instance in driver loop).
   - Same change applied to bootstrap-safe `HirLowering_dot_lower_module`.

2. `src/compiler/20.hir/hir_types.spl`:
   - `SymbolTable.define` gains a first-write-wins guard for type-kind symbols
     (Class/Struct/Enum/Trait): if the scope already has a binding for `name`,
     returns the existing `SymbolId` without overwriting. Non-type symbols retain
     last-write-wins behaviour.

3. `doc/08_tracking/feature_request/compiler_requests.md`:
   - FR-COMPILER-002 status updated to `Partially-Implemented` with partial-fix
     notes and infrastructure-blocker details.
   - FR-COMPILER-003 filed: 2-pass import resolver with `module_resolver`,
     `current_file`, `loaded_modules` fields needed in `HirLowering` before the
     Rust seed's `preregister_imported_type_names` + `load_imported_types` pattern
     can be ported.

**What remains (FR-COMPILER-003):**
- `HirLowering` needs `module_resolver: ModuleResolverPort?` + `current_file` +
  `loaded_modules` fields.
- Driver must populate these when constructing `HirLowering`.
- `lower_module` must call a new `resolve_import_symbols` pass before
  `declare_module_symbols` to scope-bind explicitly imported names.
- Without this, first-write-wins is deterministic but not import-target-aware:
  whichever module loads first in the driver loop wins the short name.

**No bootstrap run performed** (fix is a prerequisite, not sufficient alone).
