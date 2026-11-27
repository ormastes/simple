# Unit declaration table is global and keyed by bare name

Found in review of PR #9585, 2026-11-16. `unit_decl_find(name)`
(`src/compiler/10.frontend/core/types.spl:1046`) scans a process-global list of unit
names. The HIR cast lowering (`expression_core.spl`, `ExprKind.Cast`) asks it with the
target's unqualified `TypeKind.Named` text, so a class/struct in another module that
shares a name with any declared unit is misread as that unit and `x as Thing` is
lowered to a `Thing { value: x }` record construction.

Fix needed: key the lookup by the resolved symbol (lower the target first and test
whether its `SymbolId` refers to a unit declaration), or scope the table per module.
Not cheap in the current frontend (the table holds no symbol ids), so not done in
lane rb4-unitwrap.

Repro: module A `unit Meter: f64 as m`; module B `class Meter: ...` and `y as Meter`
in B -> lowered as unit construction.

Fix (lane rb5-unitsym): the HIR cast now lowers the target first and takes the unit path only when its RESOLVED symbol is a `SymbolKind.Struct` (what a unit lowers to) whose resolved name is a declared unit (`_Expressions/unit_cast_target.spl`, `cast_target_resolves_to_unit`). A same-named class/enum/alias/trait no longer matches. Residual: the table itself is still name-keyed, so a plain `struct Meters` in another module colliding with a unit name would still match. Evidence: `test/01_unit/compiler/20.hir/unit_cast_target_resolution_spec.spl` 4/4 on the deployed seed (helper level; full two-module lowering not run, pure-Simple compiler not runnable on the seed).

Status: verification-pending
