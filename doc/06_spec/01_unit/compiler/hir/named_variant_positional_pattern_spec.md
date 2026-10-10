# Named enum payload positional patterns

Executable specification:
`test/01_unit/compiler/hir/named_variant_positional_pattern_spec.spl`.

Execution status: authored; not yet run by a qualified test runner.

- Positional matching of named text and integer slots retains declaration
  order and the exact declared type of each bound child.
- A positional named-payload pattern with the wrong arity produces an HIR
  error and an error pattern.

Native behavioral fixture:
`test/fixtures/compiler/named_variant_positional_pattern.spl`.
Expected stdout is `named-positional-ok` and exit status is zero. It checks
both a unit alternative and the values of two differently typed payload slots.

Related evidence and remaining limits:
`doc/08_tracking/bug/mir_declared_variant_pattern_owner_loss_2026_10_10.md`.
