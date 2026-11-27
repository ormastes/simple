# Self-hosted compiler: same-named `unit` declarations overwrite each other

Status: fix-implemented-verification-pending (updated 2026-11-27). Found by code read,
2026-11-26; interpreter unit specs pass, while full self-hosted CLI verification
remains pending (no self-hosted full-CLI binary is deployed on this host).

## What the code does

`src/compiler/10.frontend/core/types.spl` keeps unit declarations in a pool of
parallel arrays keyed by the bare unit name:

- `unit_decl_find(name)` (line 1089) scans `unit_decl_names` for the name only.
- `unit_decl_register_origin(...)` (line 1114) calls it, and when a row with
  that name already exists (lines 1117-1124) rewrites that row's role, short
  symbol, underlying type tag, alias target and legacy origin in place and
  returns the existing index.

There is no module in the key. Two modules that each declare `unit X` with
different underlying types, suffixes or roles therefore share one row, and
the declaration registered last wins for every module in the program.

## Why it matters

The pool feeds the unit checks (`SPL-UNIT-002` family) and the suffixed
literal checks (`unit_decl_find_by_suffix`). With one row per name, a module
can be checked against another module's unit: its literals take the other
unit's suffix and its arithmetic takes the other unit's underlying type. No
diagnostic reports the collision.

The standard library already declares the same unit name in more than one
family (`unit Count: i64` in `src/lib/common/types.spl`,
`src/lib/gc_async_mut/types.spl` and `src/lib/nogc_async_mut/types.spl`). Those
three agree today, so the overwrite is invisible; it stops being invisible the
first time two same-named units differ.

The Rust seed had the neighbouring defect (a plain `type Count = i64` alias in
one module was read as the unit `Count` declared in another) and it broke
every compiled run of the window-manager module graph. The self-hosted
compiler does not have that one: it expands aliases to their target per
module before the unit check (`20.hir/hir_lowering/type_aliases.spl`).

## Unproven

- Whether the parser's flat-AST tagging keeps a plain alias that collides
  with a unit name distinct from the unit.
- A module that declares the plain alias while also importing the unit.

## Fix Implemented (2026-11-27)

- `src/compiler/10.frontend/core/types.spl`:
  - Added module ownership tracking (`unit_decl_modules`, `unit_decl_current_module`, `unit_decl_last_conflict_msg`, `unit_decl_set_current_module`, `unit_decl_get_current_module`, `unit_decl_last_conflict_error`, `unit_decl_module_at`, synced with `named_type_set_current_module` and preserved across `UnitDeclPoolSnapshot`, `type_pools_promote_hir_owners`, `flat_type_pools_restore`, and `FlatPoolState`).
  - Keyed `unit_decl_register_origin` and added `unit_decl_find_in_module` / `unit_decl_find_by_suffix_in_module` by `(declaring_module, name)`, retaining unqualified current-module-first fallback in `unit_decl_find` and `unit_decl_find_by_suffix`.
  - Refuses conflicting same-module `unit` redeclarations (`unit_decl_last_conflict_msg`) while preserving legitimate in-place `derived` refinement and legacy `newunit` re-registration.
- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`: `_parser_lower_unit_decl_checked`, `parser_lower_unit_decl`, and `parser_lower_derived_unit_decl` surface same-module declaration conflicts with a single `parser_error` and skip duplicate struct emission.
- `src/compiler/10.frontend/core/unit_scope.spl` & `src/compiler/10.frontend/core/interpreter/eval_units.spl`: `unit_suffix_declared` and `eval_suffixed_lit` respect active module ownership when checking/looking up suffixed units.

## Verification

- `test/01_unit/compiler/10.frontend/unit_decl_module_isolation_spec.spl`: `5 examples, 0 failures` (`--mode=interpreter`).
- Frontend unit regression suite (`--mode=interpreter`): `unit_decl_canonical_spec.spl` (10/10), `unit_decl_e2e_spec.spl` (9/9), `unit_scope_per_file_spec.spl` (4/4), `unit_name_conflict_warning_spec.spl` (7/7).
- Self-hosted full-CLI binary execution remains pending (`fix-implemented-verification-pending`).
