# Unit registry convert() rejects every cross-scale conversion (dimension mismatch)

- Date: 2026-08-27
- Found by: sspec modernization batch (resid6_part_02), behavioral rewrite of
  `test/03_system/app/compiler/feature/world_units_newunit_spec.spl`

## Symptom

`UnitRegistry.convert(value, from, to)` returns
`Err("dimension mismatch: cannot convert 'wunkmph' to 'wunmps'")` for two
expressions with identical factor sets (m^1 s^-1) but different scales
(1000/3600 vs 1/1).

## Root cause

`src/compiler/30.types/units/unit_registry.spl` — `dimensions_match` documents
"scale may differ — that is what `convert` multiplies through", but delegates
to `std.common.units.model.world_units.unit_expression_equivalent`
(`src/lib/common/units/model/world_units.spl:133`), which returns false unless
`exact_ratio_equal(left.scale, right.scale)`. Cross-scale conversion therefore
can never pass the dimension gate, and the `exact_ratio_div(from.scale,
to.scale)` ratio inside `convert` is dead for every non-identity-scale pair.

## Reproducing spec

`test/03_system/app/compiler/feature/world_units_newunit_spec.spl` scenario
"km/h converts to m/s through the exact 5/18 factor" (REQ-WUN-004) — RED,
legitimate failure, left failing on purpose: 18 km/h must convert to exactly
5 m/s.

## Fix direction

`unit_registry.spl` should compare factor sets only (scale-insensitive
dimension equality), keeping `unit_expression_equivalent` for exact-equality
uses, or `unit_expression_equivalent` needs a scale-tolerant sibling.
