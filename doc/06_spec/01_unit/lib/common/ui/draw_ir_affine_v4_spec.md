# Versioned affine DrawIR v4

Manual companion to
`test/01_unit/lib/common/ui/draw_ir_affine_v4_spec.spl`.
Generated SPipe output awaits a trustworthy Simple runner.

## Contract

DrawIR v4 stores a local f64 rectangle and an optional six-coefficient affine
matrix. The matrix maps local `(x,y)` to surface
`(a*x+c*y+tx, b*x+d*y+ty)`. The command carries an explicit raster policy:
`aliased-pixel-center` or `coverage-aa`. Four legacy integer geometry fields
remain zero for affine rectangles. UiIr v2 preserves the local rectangle,
matrix and policy; older execution paths must refuse the complete v4 scene.

## Scenarios and expected evidence

| Scenario | Required result |
|---|---|
| Legacy v3 one-rectangle composition | Exact pinned SDN bytes, with no affine or raster-policy fields |
| Malformed v3 fractional presence field | Checked parser returns an error rather than letting the legacy decoder panic |
| V4 affine rectangle | SDN v4 header, all six matrix values, `coverage-aa`, exact local geometry, zero legacy fields, and byte-stable round trip |
| V4 rectangle with nil matrix | Explicit `affine_present=false` and `aliased-pixel-center`; UiIr uses unchanged f64 coordinates |
| Missing or malformed matrix field, unknown policy in v4 SDN | Checked parser returns an error rather than an executable identity or partial composition |
| UiIr lowering | UiIr v2 contains the same local f64 geometry, matrix and policy |
| Nonzero legacy field or unsupported policy | UiIr rejects the whole mixed batch with empty commands and batches, locating command index 1 |
| Nonfinite or singular matrix | UiIr rejects the whole mixed batch with empty commands and batches, locating command index 1 |
| Legacy Engine2D CPU consumer | A mixed v4 batch with a valid first rectangle and later affine rectangle yields fallback and zero rendered commands |

The test uses real assertions. This manual records intended behavior and does
not claim runtime PASS or physical GPU pixel equivalence. The CPU scenario is
an expected safety contract while the legacy consumer guard is being added.

Requirements: REQ-2D-002, REQ-2D-006.
