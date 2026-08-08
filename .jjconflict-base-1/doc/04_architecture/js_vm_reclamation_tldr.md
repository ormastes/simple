# JavaScript VM Reclamation — TLDR

Status: **PROPOSED / RED — ownership ABI and SSpec contract only.**

- Production owner: `src/lib/nogc_sync_mut/js/engine/**`, reached through
  `BrowserRuntimeState`; `common/js` and the `gc_async_mut` interpreter facade
  are not implementation owners.
- Preserve the landed static lexical-parent semantics during handle migration;
  they are a prerequisite, not reclamation evidence.
- Freeze `JsHeapHandle(store_kind,slot:i64,generation:i64)`,
  `JsExternalRootKey(handle,owner_kind,owner_id)`, and
  `JsTypedEdge(kind,handle)` before implementation.
- External roots are independently keyed and reference-counted; stale
  retain/resolve/mark/release operations cannot affect a reused slot.
- At outermost host-turn safe points, `JsInterpreter` traces typed roots across
  object, function, and environment stores using an iterative worklist.
- `handle.store_kind` selects the object/function/environment store;
  `JsTypedEdge.kind` records only the semantic edge family.
- The operative `JsValue` has no `Symbol`; delete stale `JsValue.Symbol` match
  arms during migration instead of adding a speculative symbol variant/store.
- Browser roots include listener callbacks **and `target_object_id`**, all
  `BrowserRuntimeState` IDs, active executor IDs, and temporary returned values.
- Collection is inhibited/deferred during execution, recursion, async drains,
  exception unwind, and listener mutation.
- Replace numeric ownership IDs such as `__simple_typed_array_buffer` with
  typed side-table edges before sweep; property-name inference is forbidden.
- Migrate every reference boundary atomically; mixed raw-ID/handle mode is RED.
- Preserve live IDs; sweep with tombstones/free lists and generation checks.
  Observe allocated/live/high-water/capacity/reclaimed counters for objects,
  functions, environments, globals, and properties.
- Treat native/bound/class/WASM function-indexed tables as weak metadata:
  values trace only from live keys and dead-key rows are removed.
- Give globals a dedicated binding store with set/delete and scoped
  save/restore APIs; object properties remain owned by `ObjectStore`.
- Share Event native methods once per runtime and scope the global `event`
  binding. Navigation/close must emit a page-disposal receipt.
- The typed inventory explicitly covers object/function/environment,
  WASM-function, pending-event, temporary-host-return, timer, Promise, stream,
  iterator, DOM, listener, and closure edges.
- Allocation/release counters are O(1); for N=128 and 2N=256, allocation scans
  stay zero and visits obey `visits_2n <= 2 * visits_n + 32`.
- The focused 1,000-cycle contract is separate from the planned external
  production 10,000-cycle gate.
- Planned modern SSpecs contribute focused evidence to
  REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008; canonical browser and
  performance gates remain required for closure.

Full design: [js_vm_reclamation.md](js_vm_reclamation.md)
