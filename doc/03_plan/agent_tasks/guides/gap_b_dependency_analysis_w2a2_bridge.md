# Guide B1 — dependency_analysis W2-A2: make `load_module_lazy` register a real module

Owner: one sonnet-class agent (compiler frontend). Follow literally.

## Measured state (2026-09-05, debug seed)

`build/probe`-style driver calling the real functions:

```
gate=0  before=0  rc=0  after=0
```

`load_module_lazy("compiler.00.common.dependency.graph", "test/03_system/plan_acceptance/dependency_analysis_spec.spl")`
returns 0 (failure) and leaves `lazy_module_known(...)` at 0. The acceptance
spec therefore fails its third scenario — honestly.

## File

`src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl`

- `load_module_lazy` (:403) — entry point. With the gate OFF (`lazy_parse_enabled() == 0`)
  it must still be able to register the module (whole-file fallback via
  `_lazy_load_whole`) and return 1; with the gate ON it must outline-scan and
  register body spans. Find which branch returns 0 for the module above by
  adding a temporary `print` at each `return 0` / `return _lazy_load_whole(...)`
  site, run the probe, then remove the prints.
- `_lazy_mod_set[module_name] = true` (around :465) is the registration the
  spec's `after == 1` reads; make sure the successful path reaches it.

## Acceptance

```
src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/dependency_analysis_spec.spl
```

All three `it`s pass:
- gate default 0 / `SIMPLE_LAZY_PARSE=1` → 1 / `"0"` → 0;
- `lazy_scan_probe(".../graph.spl")` starts with `ok:` and names
  `importgraph_new`, `importgraph_add_edge`, `importgraph_find_cycles`; a
  nonexistent path yields `unreadable: <path>`;
- `lazy_module_known` flips 0 → 1 across a `load_module_lazy` call that
  returns 1.

Discard any run containing `E1034`. Do NOT change any `expect` in the spec.
Then tick the plan's W2-A2 box in `doc/03_plan/compiler/dependency_analysis/plan.md`
ONLY with `— verified <command> → 3 examples, 0 failures, <date>` appended.
