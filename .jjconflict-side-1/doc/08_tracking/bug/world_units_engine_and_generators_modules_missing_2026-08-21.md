# `std.common.units.engine` and `std.common.units.generators` do not exist — two specs cannot load

- Date: 2026-08-21
- Status: OPEN (unimplemented feature, not a regression in the specs)
- Severity: medium — two unit specs are unrunnable; the unit-expression parser
  and the world-unit seed importers have no implementation at all.

## Symptom

Both specs report `1 total, 0 passed, 1 failed` with **zero examples executed**
(a file-level load ERROR, not an assertion failure):

```
test/01_unit/lib/common/units/engine/unit_expr_spec.spl
  error: semantic: Cannot resolve module: std.common.units.engine.unit_expr
  SPEC FILE VERDICT: ... outcome=ERROR declared>=4 executed=0

test/01_unit/lib/common/units/generators/world_units_importers_spec.spl
  error: semantic: Cannot resolve module: std.common.units.generators.world_units_importers
  SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=0
```

Mirrors under `test/unit/...` carry the identical text.

## Root cause — the product modules were never written

`src/lib/common/units/` contains exactly two subdirectories:

- `catalog/world_units_v1.sdn`
- `model/world_units.spl`

There is no `engine/` and no `generators/` directory anywhere in the tree, and
`git grep -l parse_unit_expression -- 'src/*'` and
`git grep -l import_all_world_unit_seed_rows -- 'src/*'` both return **nothing**
— the symbols the specs import are not defined in any source file, so this is
not a moved module or a renamed import.

What *does* exist is the model layer the specs build on:
`src/lib/common/units/model/world_units.spl` defines `ExactRatio` (:24),
`UnitFactor` (:28), `UnitExpression` (:32), `UnitIdentity` (:164),
`UnitAlias` (:170) and `unit_expression_factor_exponent` (:124). So the data
model is in place; the two consumers of it are missing.

## Missing surface (from the specs, which are correct as written)

`std.common.units.engine.unit_expr`:
- `parse_unit_expression(text) -> {ok, expression, error}` — must handle `km/h`
  (scale 5/18, metre^1, second^-1), the alias `kmph`, the chemistry alias `M`
  (scale 1000, mole^1, metre^-3), and must report
  `"unknown unit expression"` for `USD/h`.
- `format_unit_expression(UnitExpression) -> text` — canonical form, e.g.
  `kmph` -> `km/h`, `M` -> `mol/L`.

`std.common.units.generators.world_units_importers`:
- `import_all_world_unit_seed_rows()` -> 10 rows
- `imported_rows_have_unique_ids(rows) -> bool`
- `imported_rows_to_sdn(rows) -> text`, carrying the source attributions
  `UCUM`, `ISO 4217/SIX`, `UNECE Rec 20`, `IUPAC Gold Book`, `IEC 80000-13`
  and the rows `symbol: "KiB"`, `code: "DZN"`, `code: "840"`.

## Disposition

Both specs are left RED per `.claude/rules/testing.md` ("a correct spec that
fails is a legitimate artifact"). They are **not** stale source-text pins:
they assert real behaviour against a real (existing) model layer, and the
implementation is simply absent.

Unblock condition: implement the two modules above under
`src/lib/common/units/engine/unit_expr.spl` and
`src/lib/common/units/generators/world_units_importers.spl`.

## No seed (Rust) change is required.
