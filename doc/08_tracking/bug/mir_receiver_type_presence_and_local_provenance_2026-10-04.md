# MIR receiver type presence and local provenance

Status: source repair; native regressions UNRUN.

The six-product helper builds using producer SHA-256
`776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`
and source `9737d1217bc44439b56bba6c2ef16faaff51bd20` report unresolved
Result predicates/payload methods, nullable text methods, and explicit enum
constructors. The retained per-backend `helper-mir-diagnosis.json` packets
classify these separately from missing array mutation lowering. They do not
prove a single cause for all receiver failures.

## Proven source defect

`HirExpr.has_type_` is the documented presence authority. The MIR owner
`enum_match_expr_type` nevertheless consumed any non-nil `type_`, including
an absent expression type's Unit placeholder, before trying the declared
symbol or function-local metadata. It also preferred the raw symbol type to
the concrete local binding, unlike `receiver_declared_type`.

The repair checks the presence bit and prefers concrete local provenance to
raw symbol metadata for Var and NamedVar. Infer/Error metadata continues to
fall through. Explicit concrete expression types remain authoritative. No
method spelling grants Result storage, no ABI/schema changes are made, and
no source or cache authority is bypassed.

`receiver_type_transport_spec.spl` has nine direct owner scenarios (ten
assertions): absent placeholders; local Result/text versus stale raw symbols;
explicit types; incomplete local and expression types; declared function
return transport; and an unknown symbol. These are authored, not executed.
Source review found no P0/P1 issue. Actual helper recovery requires a rebuilt
producer and preserved native replay; it is not yet established.

## Separate remaining groups

The current MIR MethodCall dispatcher passes empty static-owner hints, so
colliding enum variant leaves cannot recover an explicit enum owner. HIR
should retain the typed enum construction through the existing EnumLit
representation, preserving actual static methods and payload semantics.

`env_ops._is_windows_platform` calls text methods on `text?` after a nil test;
flow-sensitive narrowing is a separate requirement. Neither that issue nor
the entire imported Result/nominal method chain is claimed fixed here.
