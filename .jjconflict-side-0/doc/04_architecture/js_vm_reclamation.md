<!-- codex-architecture -->
# JavaScript VM Reclamation Architecture

Status: **RED — design only; no collector or executable evidence exists.**

## Scope and selected owner

This design fixes the append-only VM growth tracked by
[`js_event_dispatch_vm_growth_2026-07-29.md`](../09_report/js_event_dispatch_vm_growth_2026-07-29.md).
The production browser reaches `src/lib/nogc_sync_mut/js/engine/**` through
`BrowserRuntimeState` in `src/lib/gc_async_mut/web/browser_session.spl`.
`src/lib/gc_async_mut/js/engine/interpreter.spl` is only a compatibility facade.
No collector, store, or alternate implementation may be added under
`src/lib/common/js/**` or the facade.

The design contributes focused reclamation evidence to
REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008; it does not by itself
close those broader production-browser requirements. It preserves JavaScript
identity and lexical closure semantics while bounding unreachable page-owned
state.

Current implementation map:

- `src/lib/nogc_sync_mut/js/engine/interpreter_types.spl`: environments and
  function closure IDs;
- `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl`: object/prototype and
  parallel property storage;
- `src/lib/nogc_sync_mut/js/engine/interpreter.spl`: interpreter-owned root
  tables;
- `src/lib/nogc_sync_mut/js/engine/runtime.spl`: public runtime/call boundary;
- `src/lib/gc_async_mut/web/browser_session.spl`: `BrowserRuntimeState` and
  `BrowserDomCallableListener`;
- `src/lib/gc_async_mut/web/browser_session_runtime.spl`: active event executor,
  dispatch, navigation, and close;
- `src/lib/gc_async_mut/js/engine/interpreter.spl`: export-only compatibility
  facade, never a collector owner.

## Ownership layers

| Layer | Owns | May call | Must not own |
|---|---|---|---|
| Browser session | `BrowserRuntimeState`, DOM/listener IDs, active executor roots, page disposal | runtime host-turn API and browser root builder | mark bits, sweep policy, slot compaction |
| `JsRuntime` | host-turn boundary and inhibit/defer protocol | interpreter safe-point API | browser DOM discovery |
| `JsInterpreter` | root union, weak-table processing, and collection orchestration | typed stores | browser state or store internals |
| Global binding store | live named bindings, scoped replacement tokens, deleted-slot reuse, global counters | value marker supplied by orchestrator | browser event semantics or object properties |
| Typed stores | allocation, iterative graph marking, stable-ID sweep/free-list reuse | only their own storage and typed cross-edge visitor | browser roots or whole-VM orchestration |

Frozen, non-overlapping APIs:

```text
EnvironmentStack.create_env(parent_env_id)
EnvironmentStack.mark_environment_graph(...)
EnvironmentStack.sweep_unmarked_environments(...)
ObjectStore.alloc_object(...)
ObjectStore.mark_object_graph(...)
ObjectStore.sweep_unmarked_objects(...)
JsFunctionStore.alloc_function(...)
JsFunctionStore.mark_function_graph(...)
JsFunctionStore.sweep_unmarked_functions(...)
JsGlobalBindingStore.set(name, value)
JsGlobalBindingStore.delete(name)
JsGlobalBindingStore.push_scope(name, value)
JsGlobalBindingStore.restore_scope(token)
JsGlobalBindingStore.mark_live_values(...)
JsInterpreter.reclaim_at_safe_point(JsVmRoots)
JsRuntime.begin_host_turn()
JsRuntime.end_host_turn(roots)
JsRuntime.push_scoped_global(name, value)
JsRuntime.restore_scoped_global(token)
browser_js_vm_roots(state, executor)
```

`JsInterpreter.reclaim_at_safe_point` is the sole graph orchestrator. Browser
code never sweeps or compacts stores; stores never discover
`BrowserRuntimeState`. The two runtime scoped-global calls are host facades that
delegate exclusively to `JsGlobalBindingStore`; they do not own storage or
marking.

## Correctness prerequisite: lexical parents

`EnvironmentStack.create_env(parent)` currently ignores `parent`, and variable
lookup falls directly from the current frame to global scope. Before
reclamation can be enabled, every environment must store `parent_env_id`;
`get_var` and `set_var` must walk that real lexical chain. The environment mark
visitor follows the parent edge and every binding value. A function follows
its `closure_env` edge. Tests must first lock shadowing, nested capture, and
post-return closure behavior; reclamation remains disabled if those tests fail.

## Complete typed root inventory

`JsVmRoots` is typed: object, function, environment, symbol, and `JsValue`
roots are distinct. A raw integer is never guessed to be an object edge.

Strong interpreter roots include:

- global/current environments; every active call frame and its environment,
  receiver, arguments, locals, return value, and thrown value;
- live global binding values; function closure environments; Node require-cache
  values and the last-cache value;
- Promise, Response, ArrayBuffer, Uint8Array, and DataView
  constructor/prototype IDs;
- pending async request objects/registry; promise tasks, handlers, and
  registrations; timer callback IDs, callback arguments, and timer-handle
  object IDs;
- host window/document/body/location/navigator/chrome/storage/promise IDs;
  host document title/cookie and body HTML/text `JsValue`s; host DOM element
  list, element, and style IDs;
- pending host-event target IDs and callback values; any host-returned
  `JsValue` until its caller consumes or explicitly releases it.

Browser roots include all IDs in `BrowserRuntimeState`: window, document, body,
location, history, navigator, chrome, session/local storage, DOM node/element
maps, element list, styles, and every listener `callback` **and
`target_object_id`**. During dispatch they additionally include every
`BrowserDomEventExecutor` node/element ID, window/document/target/event ID and
callback/argument value. Pending listener operations are applied before roots
are frozen.

Function-indexed metadata is weak, not a root source. `native_id_map`, the
parallel bound-function tables, class-prototype mappings, and WASM export
function/import/module/body tables are visited only after their key function
has been marked from a strong root. Their target/receiver/argument/import/
prototype/module values are then marked, and rows whose key remains dead are
removed in lockstep before function-slot reuse. This prevents bookkeeping from
retaining every historical function or module.

The marker uses an iterative typed worklist. Objects mark prototypes and every
property `JsValue`; functions mark their closure environment and typed
function-owned edges; environments mark parents and binding values. Cycles are
safe because each typed ID is marked once.

## Numeric backing-ID migration gate

Ownership-bearing IDs stored as `JsValue.Number`, including
`__simple_typed_array_buffer`, `__simple_data_view_buffer`,
`__simple_stream_pending_pipe_dest`, `__simple_stream_source_id`,
`__simple_uint8_iterator_source_id`, `__simple_wasm_streaming_target`,
`__simple_wasm_runtime_memory_buffer`, `__simple_timer_callback_id`, and
dynamic `__simple_handler_next:*` links, are invisible to a typed tracer and
could be reclaimed or reused incorrectly. WebGPU/module IDs and every other
numeric `*_id` property must be classified as either an external scalar handle
or a VM ownership edge. Before sweep is enabled, every ownership edge must
move to a typed side table owned by its store, or become an explicitly
registered typed root. A static inventory test rejects unclassified or newly
introduced numeric ownership edges. Until this migration is complete the
collector gate is RED.

## Stable IDs and collection

Object properties are parallel arrays today. Sweep removes/tombstones all
parallel entries in lockstep, clears prototypes, and returns dead slots to a
free list. Objects, functions, and environments retain stable IDs for their
live lifetime; live entries are never compacted. Reused slots carry generation
validation (or an equivalent non-aliasing handle) so stale host IDs cannot
resolve to a new object.

`JsGlobalBindingStore` replaces the interpreter's parallel global name/value
arrays. `set` replaces an existing name rather than appending it; `delete`
tombstones and recycles its slot. A scope token records whether a binding was
absent plus its prior value, so `restore_scope` deterministically restores or
deletes it. Object properties remain exclusively owned and counted by
`ObjectStore`; global binding code never edits property arrays.

Each object/function/environment/global/property store reports:

- `allocated_total`: monotonic allocations, including reused slots;
- `live`: currently reachable/allocated entries;
- `live_high_water`: maximum live count;
- `slot_capacity`: allocated backing slots;
- `reclaimed_total`: cumulative reclaimed entries.

VM statistics also expose `collection_count` and `deferred_collection_count`.
The test oracle compares `live` and `slot_capacity`; filtering counters or
reporting only monotonic totals cannot close the bug.

## Safe points and deferred collection

`JsRuntime.begin_host_turn()` increments `reclaim_inhibit_depth`.
`end_host_turn(roots)` decrements it and may collect only when:

1. the outermost host turn has ended;
2. the interpreter call stack is empty;
3. pending listener operations have drained; and
4. the complete browser root snapshot and temporary host-return roots exist.

Evaluation, callable/native execution, recursive event dispatch, timer and
microtask draining, exception unwind, and listener-operation drain all inhibit
collection. A request made while inhibited sets `reclaim_deferred`; the next
valid outermost safe point performs one collection and clears it. This prevents
mid-stack reclamation and bounds duplicate work.

## Event dispatch and disposal

The three host Event methods are allocated once per runtime and shared. Each
dispatch allocates only the Event instance and necessary transient data. The
global `event` binding is scoped: save, bind, then restore or delete; it is not
append-only. Browser dispatch uses the runtime scoped-global facade, never
interpreter arrays. If script stores the Event or a closure captures it,
ordinary root tracing preserves its identity and fields.

Navigation replacement and `BrowserSession.close()` explicitly dispose the old
page VM, cancel/drain callbacks, collect or destroy all page-owned stores, and
record a disposal receipt before dropping `runtime_state`. A callback from the
old generation cannot enter the new runtime.

## Verification boundary

Planned executable evidence lives only at:

- `test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl`
- `test/02_integration/browser/js_event_vm_reclamation_spec.spl`
- `test/03_system/feature/web_platform/js/js_event_dispatch_vm_reclamation_spec.spl`

The detailed mappings and exact oracles are in
[`js_event_dispatch_vm_reclamation.md`](../03_plan/sys_test/js_event_dispatch_vm_reclamation.md).
The canonical broader browser gate remains
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`,
with production budgets in
`test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`.
All new reclamation evidence is absent/unimplemented at this design checkpoint,
so overall status is RED.

## Risks and fail-closed gates

- An unregistered host raw ID or generation-reuse alias can become use-after-
  free; typed registration and stale-handle negative tests are mandatory.
- Numeric hidden ownership IDs can sever live buffer/view graphs; sweep stays
  disabled until their inventory is zero.
- Native, bound, WASM, Promise, timer, async, and cache tables can retain stale
  entries; their typed edge visitors and sweep cleanup need focused tests.
- Parallel property arrays can desynchronize; invariant checks run before and
  after sweep.
- Recursive marking or collection during execution can overflow or corrupt
  state; only iterative marking at the frozen safe point is allowed.
- Implementing in `common/js` or the compatibility facade would leave the
  selected browser engine leaking; owner-path tests reject that layout.
