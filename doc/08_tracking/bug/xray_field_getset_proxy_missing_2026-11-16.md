# XRay field get/set virtual proxy does not exist (feature gap) — 2026-11-16

Status: open (feature request). Owner request 2026-11-16.

## Request
XRay aspect work should intercept field/property get and set through a virtual
get/set proxy, generated ONLY when the XRay aspect is enabled and the class has
a get/set pointcut. Off: no proxy symbol, no wrapper, no indirection, and a field
access path identical to a no-aspect build.

## Found (worktree from origin/release/1.0.0, 2026-11-16)
- XRay is function-granular: LLVM `function-instrument` attrs / native sleds
  (`70.backend/backend/_MirToLlvm/core_codegen.spl`), selection by function
  name (`simple.trace/observer-v1.pointcuts`), edges function->function
  (`src/lib/common/trace/trace_edge_select_v1.spl`, `.edges`).
- `10.frontend/aspect_registry.spl` records `@advice(KIND, SELECTOR)` on
  functions only; `10.frontend/core/aop.spl` has no field-access join point.
- No `virtual_get`/`virtual_set`/property-proxy symbol anywhere in
  `src/compiler` or `src/lib`. Field get/set lowering (`eval_field_access`,
  `cg_field_access_expr`, MIR field ops) has no aspect hook.
- `trace_edge_spec_parse_v1("edge field get=...")` is rejected (Err).

## Needed (not built — owner sign-off required, non-trivial)
1. Pointcut kind `get(Class.field)` / `set(Class.field)` in the aspect/predicate grammar.
2. HIR/MIR lowering that rewrites matched field accesses to a proxy call only when
   XRay is on; off must be byte-identical (IR diff vs no-aspect build).
3. A field-access trace event/edge kind in `observer_contract_v1`.

## Spec
`test/01_unit/lib/xray/xray_getset_proxy_spec.spl`: 1 pass (grammar rejects field
selectors today), 3 fail-fast RED rows (a) on-routes-through-proxy, (b) off-identity,
(c) no-pointcut-no-proxy.
