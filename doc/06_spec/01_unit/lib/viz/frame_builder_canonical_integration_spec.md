# Canonical Viz frame-builder integration

The executable test at `test/01_unit/lib/viz/frame_builder_canonical_integration_spec.spl` verifies that `frame_builder_new()` produces canonical entity frames usable as an `AggregatorEntry` and retrievable through `DisplayCompositor`.

It verifies canonical root selection, one valid shared-quad-state index per appended solid quad, typed referenced-surface identity, and fail-closed handling of open/nested passes, invalid mailboxes, nonfinite geometry, and forward render-pass references. This is compositor-model evidence only; GPU backend execution remains a separate gate.
