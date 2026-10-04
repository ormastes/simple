This fixture must be compiled through the native entry-closure route for each
backend and then executed. It imports `inner.spl` only inside function bodies.

- `main.spl`: exit 0 and exact stdout `local-use: 15 checks passed` followed by a
  newline. It checks aliases, outer-name shadowing, repeated imports in separate
  functions, nested-block scope restoration, and a lazy import. Enum payloads,
  classes, and type aliases use different representations in the outer and
  inner modules so a wrong declaration owner cannot accidentally pass.
- `leak_rejected.spl`: compilation must fail with `unresolved name: selected` in
  `main`; `owner` importing the alias must not expose it to another function.
- `test/01_unit/compiler/frontend/flat_ast_local_use_spec.spl`: three cases
  check retained aliases, lazy metadata, and cache round-trip after pool reuse.

Source inspection is not a substitute for these compile/run results. No native
result is recorded by adding this fixture.
