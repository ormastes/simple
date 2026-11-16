# unit_ops has no dimension quotient: Distance / Duration is denied, not velocity

- Date: 2026-11-15
- Plan rows: RB-UNIT-01/02 (robust boundaries plan 2.4)
- Status: open (spec RED, fix not minimal)
- Repro: `test/01_unit/compiler/units/unit_dimension_parity_spec.spl`, case
  "distance / duration yields a velocity dimension through unit_ops".

`unit_op_verdict("div", "Distance", "Duration")` returns `Deny` (SPL-UNIT-002,
"distinct units never mix implicitly"). The dimension algebra (km/hr = 5/18 m/s,
metre^1 second^-1) exists only in `std.common.units.model.world_units` and the
`UnitRegistry`; the shared verdict table consulted by the compiler gate and the
interpreter has no declared-quotient rule or per-unit dimension vector.

Fix needs a design decision (declared quotient rows or dimension vectors on
`UnitDecl`, plus result-unit naming and scale), so it is not a minimal change.
Prevention: the spec stays RED until unit_ops approves the quotient.
Passing in the same spec: km/hr scale 5/18, exact 1/2, `km + kg` deny,
same-storage nominal units deny.
