# Immutable/async checks: open questions the plan does not define (2026-11-15)

Status: open (decision needed). Plan:
`doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md` section 3.2.

## 1. `E_INIT_CAPABILITY_ESCAPE` — not implemented

Plan text: "Producer or mutable alias illegally escapes its region -> Compile
error `E_INIT_CAPABILITY_ESCAPE`". The plan never defines "region". Undecided:
- Is the region a function body, an `async` scope, the construction expression,
  or the arena/epoch of the node?
- Which escapes count: returning the producer/partially initialized node,
  storing it in a field or global, capturing it in a closure, passing it to a
  callee that is not itself `@support_async_immutable`?
- Is a mutable alias of a node whose field is pending an escape of the node
  (section 3.1: "registered before the partially initialized node escapes")?
No semantics were invented; the code is absent, no spec was added.
Needed from the owner: one-sentence region definition + the escape list.

## 2. `E_ATTR_NOT_READY` — implemented for the narrow, statically evident case

Implemented (`required_field_init_v1.spl`, spec
`test/01_unit/compiler/hir/attr_not_ready_v1_spec.spl`): a field bound with
`f: async <expr>` at a construction in the same function, read through that
local as `local.f` without `await`. Error in every gate mode (the
`@support_async_immutable` annotation is the opt-in, like `E_ASYNC_INIT_*`).
Not defined by the plan, so not implemented:
- "proven readiness" other than `await` (a completion check, a group-ready
  barrier, a prior `await` of the same field dominating the read);
- flow through aliases, `Immutable<T>` views (`b.immutable()`), parameters,
  returns and fields of other nodes;
- a standalone `val p = async <expr>` value used before await (section 3 only
  specifies pending FIELD reads).

## 3. Observation: statement-start `await x.f` does not lower to `Await`

In a plain `fn`, `await n.inferred` as a bare tail/statement expression did not
reach the verifier as `HirExprKind.Await` (the fixture needed
`val r = await n.inferred`, which does). `async fn` fixtures made the verifier
report nil in the spec harness. Cause not investigated; only that behaviour was
observed. Needs a repro in the parser/lowering lane. Until fixed, a
statement-position `await n.f` is a false positive of `E_ATTR_NOT_READY`.
