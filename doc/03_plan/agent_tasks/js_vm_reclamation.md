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
