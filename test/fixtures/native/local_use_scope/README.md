This fixture must be compiled through the native entry-closure route for each
backend and then executed. It imports `inner.spl` only inside function bodies.

- `main.spl`: exit 0 and exact stdout `local-use: 6 checks passed` followed by a
  newline. It checks aliases, outer-name shadowing, repeated imports in separate
  functions, nested-block scope restoration, and a lazy import.
- `leak_rejected.spl`: compilation must fail with `unresolved name: selected` in
  `main`; `owner` importing the alias must not expose it to another function.
- `test/01_unit/compiler/frontend/flat_ast_local_use_spec.spl`: two parser cases
  check retained aliases and lazy metadata with no module-level import added.

Source inspection is not a substitute for these compile/run results. No native
result is recorded by adding this fixture.
