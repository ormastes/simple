# Immutable/async checks: open questions the plan does not define (2026-11-15)

Status: open (decision needed). Plan:
`doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md` section 3.2.

**Owner decision needed now: see "Decision needed" at the start of section 4** (the
region for `E_INIT_CAPABILITY_ESCAPE`). Section 1 is superseded by section 4: a
provisional, default-off implementation landed in PR #9311.

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

## 4. `E_INIT_CAPABILITY_ESCAPE` — PROVISIONAL region definition (2026-11-15, owner to ratify)

### Decision needed

**Question:** when a field is filled later by an async producer, which values handed to that producer should be a compile error because they can still change after the constructing function returns?

```
var counter = 3
HirNode(id: 1, body: "b", inferred: async_init(counter))   # with SIMPLE_INIT_CAPABILITY_ESCAPE=on: E_INIT_CAPABILITY_ESCAPE
# `val counter = 3` or `async_init(7)` -> accepted; switch off (default) -> nothing reported
```

Options:
1. **Ratify the current rule** ("region" = the constructing function's borrow boundary; error = a `var` local passed directly to `async_init(...)`). Cheap and already landed off-by-default. Caveat: it also flags plain value types like `i64`, which are copied, so it can reject code that is actually safe.
2. **Widen it to real aliases only:** error when a mutable *reference* (`var` object, `&mut`/`me` parameter, closure capture, nested sub-expression) reaches the producer; copied values are fine. Fewer false errors, more escapes caught, but needs type information and more work.
3. **Drop the check** (delete the provisional code and spec); rely on the borrow checker and `E_ATTR_NOT_READY`. No new errors, but nothing stops a producer reading state the caller later mutates.

**Recommendation: option 2, with option 1 kept as the interim default-off step.** The danger is shared mutable state, not a `var` keyword; flagging copied scalars would teach users to ignore the error. Also answer: do `me`/`&mut` parameters count (recommended: yes).

Verified 2026-11-15 against `required_field_init_v1.spl:238-252,284-293` and `init_capability_escape_v1_spec.spl`: the description below is accurate; correction added: the check does not look at the argument's type, so a copied scalar `var` is flagged too.

An anchor exists, so a definition is proposed (not ratified). The borrow checker
already has a region: the **short-borrow boundary**, enforced by
`record_loan_escape` (`src/compiler/55.borrow/borrow_check/borrow_graph.spl`,
call sites in `borrow_check/mod.spl`: stored in an aggregate field / global,
captured by or sent to a spawned task, "retained in a promise body", sent to an
actor mailbox, returned, exception payload).

Proposed: the region is the constructing function's short-borrow boundary. An
async producer (`f: async <expr>`, i.e. `async_init(<expr>)`) runs after that
boundary, so a mutable alias captured by the producer escapes it.

Implemented, default OFF, narrowest case: `SIMPLE_INIT_CAPABILITY_ESCAPE=on`
makes a `var` local named directly as an argument of the `async_init(...)`
producer of an authorized pending field an `E_INIT_CAPABILITY_ESCAPE` row
(`required_field_init_v1.spl`, spec
`test/01_unit/compiler/hir/init_capability_escape_v1_spec.spl`, 4/4; RED was 1
failed of 4). Off emits nothing and the five neighbouring immutable/async specs
are unchanged. Not covered, still undefined: captures nested inside producer
sub-expressions, aliases, closures, `me`/`&mut` parameters, and whether returning
the partially initialized node counts (section 3.1 says registration happens
before it escapes, so returning it is assumed allowed). The check works on HIR
only: the producer is an ordinary `async_init` call, so MIR/NLL never sees a
promise body for it. Needed from the owner: ratify or replace the region, and say
whether `me`/`&mut` parameters count.

## 5. REV-01 / REV-02 hooks (W8)

- REV-02 ("frozen serialization/reload -> identical, no pointers persisted"): the
  pointer-free codec hook already exists (`canonical_file_ast_encode_v1` /
  `canonical_file_ast_decode_v1`, `FileAstV1`) but had NO spec at all. Pinned now
  by `test/01_unit/compiler/cache/rev02_frozen_file_ast_codec_spec.spl` (5/5,
  GREEN on first run: no codec defect). It covers the FileAstV1 payload only;
  a generic `FrozenImmutable<T>` codec kind for arbitrary `T` is undefined in the
  plan and not implemented.
- REV-01: the reclamation hook is the SCV per-reader lease. A single pinned
  revision is GREEN; several pinned revisions in one process are RED, see
  `rev01_one_lease_per_process_blocks_multi_revision_pin_2026-11-15.md`.
  Undefined: how a `RevisionImmutable<T>` handle acquires a lease, and in-memory
  reclamation.
