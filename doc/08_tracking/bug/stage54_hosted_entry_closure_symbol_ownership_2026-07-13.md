# Stage54 hosted entry-closure symbol ownership gaps

## Observed evidence

- The failed hosted project compiles `cli__check__run_check`, but callers in the
  CLI entry/build objects retain an unresolved bare `run_check`. The existing
  reduced `use`-map test resolves this case, so the remaining defect is a
  production-scale use-map/mangling mismatch rather than a missing module.
- Consumers retain unresolved `json_serialize`, and no serializer provider
  object is emitted. `common/json/__init__.spl` exports it and reduced package
  provider tests pass, so the production entry-closure provider discovery path
  still needs a representative failing fixture or trace.
- GPU modules enter the closure through compiler backend registries. Entry
  closure is module-import based, so every function in an imported module is
  compiled even when the CLI never selects its GPU branch. Those references are
  therefore not safely removable by adding runtime stubs.
- Strict hosted linking correctly emitted no weak stubs. Converting these
  unresolved names into permissive stubs would hide closure and ownership
  defects.

## Exact blocker

A small runtime-stub ownership correction cannot fix these remaining symbols.
The next change needs a production-shaped closure regression fixture that
captures qualified `use` resolution and package-facade bare exports, followed
by either function-level reachability pruning or explicit backend feature
gating for unused GPU modules. That work is intentionally outside the minimal
native-all/core-C archive composition fix.
