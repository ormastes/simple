# JS Event Dispatch VM Reclamation System-Test Plan

Status: **PROPOSED / RED — G1 contract exists only as fail-fast SSpec design.**

## Frozen locations

1. `test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl`
2. `test/02_integration/browser/js_event_vm_reclamation_spec.spl`
3. `test/03_system/feature/web_platform/js/js_event_dispatch_vm_reclamation_spec.spl`

No executable `.spl` spec belongs under `doc/06_spec`.

## Frozen scenario vocabulary

Shared step text:

- `step("Retain independent escaped values")`
- `step("Trace typed closure roots")`
- `step("Reject stale releases after reuse")`
- `step("Reclaim without allocation scans")`

Shared helpers:

- `make_gc_ownership_fixture`
- `expect_gc_ownership_invariants`

Until implemented, the checker must call
`fail("RED: generation-safe JS VM reclamation is not implemented")`.
No `pass_todo`, empty body, boolean-wrapper assertion, counter filtering, or
Event reuse is acceptable.

## Requirement traceability and oracles

These are focused contributing checks, not complete closure of the broad
browser requirements. Canonical full-browser evidence remains
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`;
production RSS/heap/pause evidence remains
`test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`.

| Requirement | Evidence | Exact oracle |
|---|---|---|
| REQ-WEB-BROWSER-017 | focused unit statistics plus 1,000-dispatch integration contribution | After one warmup collection, object/function/environment/global/property `live` and `slot_capacity` are unchanged after 1,000 non-retaining dispatches; `live_high_water` remains within the fixture bound. `allocated_total` may increase and is never substituted for `live`. |
| REQ-WEB-BROWSER-018 | focused system navigation and close contribution | Disposal receipt identifies the old page generation; page-owned live counts are zero and old callbacks cannot execute or resolve after replacement/close. |
| NFR-WEB-BROWSER-005 | long-run production gate, linked but not satisfied by the focused spec | Browser plus renderer RSS is at most 384 MiB after 60 minutes. |
| NFR-WEB-BROWSER-006 | separately planned external 10,000-cycle production gate; focused SSpecs are precursors only | After bounded quiescence, live heap and retained browser resources are within 10% of post-warmup baseline. The unit contract does not tag or claim this row. |
| NFR-WEB-BROWSER-007 | unit deferred-collection scenario and production pause sampling | Recursive dispatch increments `deferred_collection_count`, does not collect mid-stack, and performs one collection at the next safe point; production p95 is <=8 ms and p99 <=16.7 ms with no frame backlog. |
| NFR-WEB-BROWSER-008 | focused navigation/close system contribution | No unreachable JS cycles or stale JS callbacks remain; the canonical hardening gate covers the broader renderer/Engine2D lifecycle. |
| NFR-WEB-BROWSER-014 | separately planned external 10,000-cycle production gate | No corruption or stale generation alias and quiescent RSS growth within 10%. The unit contract does not tag or claim this row. |
| NFR-WEB-BROWSER-015/016 | unit work counters plus production regression gate | Allocation/release update live counters in O(1), allocation scans equal zero, N=128, 2N=256, allowance=32, and `visits_2n <= 2 * visits_n + 32`. |

## Unit specification

The selected-owner unit spec proves:

- the public ABI is exactly
  `JsHeapHandle(store_kind,slot:i64,generation:i64)`,
  `JsExternalRootKey(handle,owner_kind,owner_id)`, and
  `JsTypedEdge(kind,handle)`;
- `store_kind` is exactly object/function/environment, edge `kind` remains
  semantic, and stale `JsValue.Symbol` match arms are deleted without adding a
  speculative Symbol value/store/root;
- the stale-Symbol static gate covers exactly
  `engine/interpreter.spl`, `engine/interpreter_async.spl`, and
  `web/browser_session_storage.spl`;
- the executable edge inventory includes `object`, `function`, `environment`,
  `wasm_function`, `pending_event`, `temporary_host_return`, and every listed
  closure/timer/Promise/stream/iterator/WASM/DOM/listener family;
- two independent owners of one escaped Event/object/function retain separate
  counts, and releasing either owner cannot release the other;
- the operation sequence `retain A, retain A, retain B, release A, release A,
  release B` yields A=`[0,1,2,2,1,0,0]` and B=`[0,0,0,1,1,1,0]`;
- stale retain, resolve, mark, and release each reject without mutating or
  enqueueing the new occupant;
- cyclic object/function/environment graphs terminate under iterative marking;
- real lexical parents preserve nested lookup, shadowing, closure capture after
  creator return, and escaped `arguments`;
- every interpreter root-table family is traversed, including bound/native,
  WASM, require cache, Promise, async, timer, stream, iterator, host DOM,
  listeners, pending event, return, thrown, and temporary host-return values;
- native/bound/class/WASM metadata values trace only when their key function is
  live, and dead-key parallel rows are removed before ID reuse;
- global `set` replaces by name, scoped restore reinstates the old value or
  deletes an absent prior binding, and repeated scopes reuse bounded slots;
- listener `target_object_id` and callback values survive while registered;
- numeric backing IDs cannot be treated as `Number` graph edges and the
  ownership-ID inventory classifies typed-array/DataView, stream/iterator,
  Promise-handler, WASM, timer-callback, and WebGPU/module ID properties and is
  empty of untyped VM ownership edges before sweep is enabled;
- stale-generation retain, resolve, mark, and release reject after slot reuse
  without changing the new occupant's root count or identity;
- all five counters are exact for objects, functions, environments, globals,
  and properties, parallel object-property arrays stay aligned, allocation
  scans remain zero, and N/2N graph visits are linear.

## Integration specification

The integration spec constructs a real `BrowserRuntimeState`, dispatches
through `BrowserDomEventExecutor`, warms once, then dispatches a non-retaining
listener 1,000 times. It compares snapshots for exact bounded `live` and
`slot_capacity`, verifies the three Event native functions were allocated only
once per runtime, and proves recursive dispatch defers collection until the
outer host turn.

The ownership matrix additionally performs 1,000 retain/release/reuse cycles
for timers, promises, streams, iterators, WASM edges, DOM nodes, and listeners.
Each row uses typed edges and generation-qualified handles; ordinary numeric
values are negative controls.

The unit work matrix fixes N=`128`, 2N=`256`, and frozen-root allowance=`32`.
It requires zero allocation scans and
`visits_2n <= 2 * visits_n + 32`. The external production budget spec, not
this unit contract, owns both 10,000-cycle NFR rows.

## System specification

The system spec runs browser HTML/JavaScript that:

1. stores the first Event and proves it is distinct from the second while its
   type, target, and fields remain unchanged;
2. retains a callback closure and proves captured locals remain valid after
   the creator invocation returns;
3. navigates to a replacement page and closes the session, checking disposal
   receipts and proving old-generation listeners cannot execute.

Independent assertions read public browser/runtime evidence; they do not infer
success from the collector's own boolean.

## Exit gate

This plan turns GREEN only when all three exact paths contain executable,
non-placeholder SSpecs and the production NFR measurements are retained. At
this docs-only checkpoint it remains RED.
