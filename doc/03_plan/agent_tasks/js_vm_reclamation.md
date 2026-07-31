# JS VM Reclamation Agent Task Plan

Status: **PROPOSED / RED — G1 ownership contract frozen; implementation is
forbidden until ABI migration review passes.**

## Frozen contracts

Implementation owner is `src/lib/nogc_sync_mut/js/engine/**`; browser
integration is `src/lib/gc_async_mut/web/**`. Frozen APIs, test paths, step text,
and helper names are defined in
[`js_vm_reclamation.md`](../../04_architecture/js_vm_reclamation.md) and
[`js_event_dispatch_vm_reclamation.md`](../sys_test/js_event_dispatch_vm_reclamation.md).
Changing them requires merge-owner review before parallel work resumes.

Frozen public data contracts:

- `JsHeapHandle(store_kind,slot:i64,generation:i64)`
- `JsExternalRootKey(handle,owner_kind,owner_id)`
- `JsTypedEdge(kind,handle)`

Frozen manual steps:

- `Retain independent escaped values`
- `Trace typed closure roots`
- `Reject stale releases after reuse`
- `Reclaim without allocation scans`

Frozen SSpec helpers:

- `make_gc_ownership_fixture`
- `expect_gc_ownership_invariants`

Incomplete helpers call `fail("RED: generation-safe JS VM reclamation is not implemented")`.

## Parallel lanes

| Lane | Scope | Files/ownership boundary | Depends on |
|---|---|---|---|
| A: ABI migration | atomically replace raw reusable references with `JsHeapHandle`; make `store_kind` select object/function/environment; delete stale `JsValue.Symbol` arms; prohibit mixed production mode | selected engine/browser reference boundaries | G1 contract |
| B: typed graph stores | `JsTypedEdge` tables for timers, promises, streams, iterators, WASM, DOM/listeners; weak metadata; lockstep sweep | selected engine stores only | A |
| C: external ownership | `JsExternalRootKey` retain counts, independent owners, stale release rejection | interpreter/runtime host-return API | A |
| D: safe points + browser roots | root union, inhibit/defer, listener/DOM executor roots, disposal receipt | interpreter/runtime/browser session | B and C |
| E: modern SSpec evidence | exact unit/integration/system paths and generated `.md` manuals | tests and `doc/06_spec/**/*.md` only | A–D behavior |
| F: performance review | O(1) counters, zero allocation scans, N=128/2N=256/+32 visit oracle, focused 1,000 cycles | read-only evidence | merged candidate |
| G: production NFR gate | separately admitted browser binary, 10,000 cycles, RSS and pause evidence | external production evidence only | A–F merged |

Agents must not implement a second collector in `common/js`, change frozen
interfaces privately, bootstrap the compiler, or claim PASS from source
inspection.

## Merge protocol

1. Merge owner: root normal/highest-capability Codex responsible for resolving API and
   root-inventory conflicts.
2. Sidecars: N/A for G1 design. Future A–E lanes may run in parallel only after
   merge-owner ABI review; each reports exact touched files and tests.
3. Merge order: A, B, C, D, E; conflict resolution stays with the merge owner.
4. Final reviewer: an independent highest-capability reviewer audits selected
   ownership, complete typed roots, semantic preservation, numeric-ID removal,
   counter oracles, and REQ/NFR traceability.
5. Fail-fast: every incomplete SSpec helper uses
   `fail("RED: generation-safe JS VM reclamation is not implemented")`; no
   placeholder PASS.

## Done conditions

- Real lexical-chain semantics pass before collection is enabled.
- Every cross-store/browser/external reference carries a generation-qualified
  handle; raw reusable IDs cannot enter production tracing or release.
- Every handle has a valid object/function/environment `store_kind`;
  `JsTypedEdge.kind` remains semantic, and stale `JsValue.Symbol` match arms are
  absent without adding a Symbol variant/store.
- The stale-Symbol deletion inventory is exactly selected-engine
  `interpreter.spl`, `interpreter_async.spl`, and browser
  `browser_session_storage.spl`.
- Independent external owners retain/release by exact key and count.
- The same-key/independent-key count sequence is
  A=`[0,1,2,2,1,0,0]`, B=`[0,0,0,1,1,1,0]`.
- Stale retain/resolve/mark/release each reject without occupant mutation.
- Numeric ownership-edge inventory is zero or explicitly typed.
- All listed stores and Browser roots participate in tracing.
- Collection occurs only at a valid outermost safe point.
- The exact three SSpec paths pass with independent oracles.
- REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008 have retained evidence.
- Navigation and close provide page-generation disposal receipts.
- Allocation-scan counters remain zero; N=128/2N=256 visits obey
  `visits_2n <= 2 * visits_n + 32`; focused 1,000 cycles are bounded.
- The 10,000-cycle requirement is closed only by Lane G's external production
  gate, never by the focused unit contract.
- Final independent review reports no blocking omission.

Until every condition holds, overall status remains RED.

## 2026-07-31 bounded first-tranche audit

Audit base: `af193d5e02b6ed35c4f553d2c1dfb6b873b19337`, including the
generation-safe contract from `ef90c16b194` and the store-kind clarification
from `f8b926e0dd5`.

Result: **RED — no independently safe A-through-E implementation tranche fits
the three-production-file limit.** The earliest safe repository-wide tranche
remains Lane A as one atomic ABI migration. It must not be split into a
generation-array-only or handle-definition-only production phase.

Evidence from the selected owner surface:

- object identity and prototypes are raw `i64` slots in
  `vm_object_store.spl`;
- function identity and `closure_env` are raw `i64` values in
  `interpreter_types.spl` and the interpreter function table;
- environment parents are raw `i64` values in `interpreter_types.spl`;
- raw object/function/environment identities cross at least fifteen current
  engine/browser production files, including evaluation, native calls, async
  records, runtime returns, DOM state, listeners, and event dispatch;
- `JsValue.Object` and `JsValue.Function` still expose raw IDs, so introducing
  generation-qualified handles in one store would create the forbidden mixed
  identity mode at every untouched boundary.

The apparent smaller slices are not independently safe:

1. Adding generations/free lists without migrating consumers permits stale raw
   IDs to alias a reused occupant. Keeping reuse disabled adds no reclamation
   behavior and creates a second dormant identity ABI.
2. External-owner refcounts cannot precede Lane A because exact keys require a
   generation-qualified `JsHeapHandle`; raw-slot keys cannot reject stale or
   foreign releases.
3. Typed mark edges cannot precede Lane A or be inferred from property names.
   Their target store is selected by `handle.store_kind`, and all listed edge
   owners must migrate before tracing can be complete.
4. Store-kind separation necessarily spans object values/prototypes, function
   values/closures, environment parents/bindings, and their runtime/browser
   boundaries; it is not an isolated object-store edit.
5. Lane E is evidence for A-D behavior and cannot be promoted while the frozen
   helper remains fail-fast RED.

Next admissible implementation is therefore a reviewed Lane A change with no
slot reuse or reclamation enabled until the raw reusable-ID inventory is zero.
Only after A lands may B and C proceed against one handle ABI, followed by D
safe points and E executable evidence. Retained browser event objects remain
unreclaimed throughout this audit.
