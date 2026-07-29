# JavaScript VM Reclamation — TLDR

Status: **RED — architecture and tests are planned, not implemented.**

- Production owner: `src/lib/nogc_sync_mut/js/engine/**`, reached through
  `BrowserRuntimeState`; `common/js` and the `gc_async_mut` interpreter facade
  are not implementation owners.
- Add real environment parents and lexical-chain lookup before enabling GC.
- At outermost host-turn safe points, `JsInterpreter` traces typed roots across
  object, function, and environment stores using an iterative worklist.
- Browser roots include listener callbacks **and `target_object_id`**, all
  `BrowserRuntimeState` IDs, active executor IDs, and temporary returned values.
- Collection is inhibited/deferred during execution, recursion, async drains,
  exception unwind, and listener mutation.
- Replace numeric ownership IDs such as `__simple_typed_array_buffer` with
  typed side-table edges before sweep.
- Preserve live IDs; sweep with tombstones/free lists and generation checks.
  Observe allocated/live/high-water/capacity/reclaimed counters for objects,
  functions, environments, globals, and properties.
- Treat native/bound/class/WASM function-indexed tables as weak metadata:
  values trace only from live keys and dead-key rows are removed.
- Give globals a dedicated binding store with set/delete and scoped
  save/restore APIs; object properties remain owned by `ObjectStore`.
- Share Event native methods once per runtime and scope the global `event`
  binding. Navigation/close must emit a page-disposal receipt.
- Planned modern SSpecs contribute focused evidence to
  REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008; canonical browser and
  performance gates remain required for closure.

Full design: [js_vm_reclamation.md](js_vm_reclamation.md)
