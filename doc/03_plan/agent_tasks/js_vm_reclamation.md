# JS VM Reclamation Agent Task Plan

Status: **RED — planning only.** Merge owner and final reviewer must not mark
this complete until executable evidence is green.

## Frozen contracts

Implementation owner is `src/lib/nogc_sync_mut/js/engine/**`; browser
integration is `src/lib/gc_async_mut/web/**`. Frozen APIs, test paths, step text,
and helper names are defined in
[`js_vm_reclamation.md`](../../04_architecture/js_vm_reclamation.md) and
[`js_event_dispatch_vm_reclamation.md`](../sys_test/js_event_dispatch_vm_reclamation.md).
Changing them requires merge-owner review before parallel work resumes.

## Parallel lanes

| Lane | Scope | Files/ownership boundary | Depends on |
|---|---|---|---|
| A: environment + unit TDD | real lexical parents, typed environment graph, closure/arguments tests | `interpreter_types.spl`, environment store, unit spec | frozen APIs |
| B: object/function stores | stable handles, typed iterative marking, weak keyed native/bound/class/WASM metadata, lockstep property sweep, counters | selected engine stores only | numeric-edge inventory |
| C: interpreter/runtime safe point | `JsVmRoots`, global binding store/scoped facade, root union, inhibit/defer, host-turn API, stats | interpreter/runtime only | A and B contracts |
| D: browser integration | root builder including listener target IDs, Event method sharing through scoped-global facade, disposal receipt | browser session/runtime only | C public APIs |
| E: modern SSpec evidence | exact unit/integration/system paths and generated `.md` manuals | tests and `doc/06_spec/**/*.md` only | A–D behavior |
| F: static/performance review | root completeness, numeric ownership scan, pause/RSS/bounded-growth evidence | read-only evidence | merged candidate |

Agents must not implement a second collector in `common/js`, change frozen
interfaces privately, bootstrap the compiler, or claim PASS from source
inspection.

## Merge protocol

1. Merge owner: primary implementation agent responsible for resolving API and
   root-inventory conflicts.
2. Sidecar lanes: A–E may run in parallel after contracts freeze; each reports
   exact touched files and tests. If no sidecar is available, record `N/A`
   rather than silently merging scopes.
3. Merge order: A, B, C, D, E; conflict resolution stays with the merge owner.
4. Final reviewer: an independent highest-capability reviewer audits selected
   ownership, complete typed roots, semantic preservation, numeric-ID removal,
   counter oracles, and REQ/NFR traceability.
5. Fail-fast: every incomplete SSpec helper uses
   `fail("RED: JS VM reclamation not implemented")`; no placeholder PASS.

## Done conditions

- Real lexical-chain semantics pass before collection is enabled.
- Numeric ownership-edge inventory is zero or explicitly typed.
- All listed stores and Browser roots participate in tracing.
- Collection occurs only at a valid outermost safe point.
- The exact three SSpec paths pass with independent oracles.
- REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008 have retained evidence.
- Navigation and close provide page-generation disposal receipts.
- Final independent review reports no blocking omission.

Until every condition holds, overall status remains RED.
