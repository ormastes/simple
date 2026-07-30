<!-- codex-design -->
# JavaScript VM Reclamation Detail Design

Status: **PROPOSED / RED — design and fail-fast SSpec contract only.**

## Requirement basis

The selected requirements already authorize this design:
REQ-WEB-BROWSER-017/018 and NFR-WEB-BROWSER-005..008/014–016. No requirement
selection changes are needed. This document does not claim a collector,
runtime execution, docgen result, pause/RSS result, or implementation
completion.

## Frozen interfaces

```text
JsHeapHandle(store_kind,slot:i64,generation:i64)
JsExternalRootKey(handle,owner_kind,owner_id)
JsTypedEdge(kind,handle)
```

These names and fields are ABI, not illustrative pseudonyms.

### `JsHeapHandle`

- `store_kind` is the closed `object`/`function`/`environment` store
  discriminator.
- `slot` indexes one lifetime within the store selected by `store_kind`.
- `generation` identifies exactly one lifetime of that slot.
- Resolution checks bounds, liveness, and exact generation.
- Reclamation increments generation before publishing a slot to the free list.
- A generation that cannot advance retires its slot permanently.

### `JsExternalRootKey`

- `handle` is the retained lifetime, not a raw slot.
- `owner_kind` names the host ownership family: returned value, DOM bridge,
  listener registration, pending event, timer, Promise, stream, iterator, or
  WASM bridge.
- `owner_id` is a stable owner/lease identity allocated in O(1).
- The root table stores an independent retain count per exact key. Releasing
  one key cannot remove another owner's key even when both retain one handle.

The executable owner sequence is:

| Operation | Key A count | Key B count |
|---|---:|---:|
| initial | 0 | 0 |
| retain A | 1 | 0 |
| retain A | 2 | 0 |
| retain B | 2 | 1 |
| release A | 1 | 1 |
| release A | 0 | 1 |
| release B | 0 | 0 |

### `JsTypedEdge`

- `kind` is a closed semantic edge-family discriminator.
- `handle` is generation-qualified.
- The marker switches on `handle.store_kind` to select storage and preserves
  `kind` as edge semantics; it never parses a JavaScript number or property
  name to discover ownership.

The exact initial edge inventory is `object`, `function`, `environment`,
`closure_environment`, `timer_callback`, `timer_argument`, `promise_task`,
`promise_handler`, `promise_registration`, `stream_source`,
`stream_destination`, `iterator_source`, `wasm_module`, `wasm_import`,
`wasm_export`, `wasm_function`, `dom_node`, `dom_style`, `listener_target`,
`listener_callback`, `pending_event`, and `temporary_host_return`.

## Atomic ABI migration

The implementation change is one atomic migration:

1. Add generation arrays, O(1) live counters, and free lists to the selected
   `nogc_sync_mut` object, function, and environment stores.
2. Change internal reference-bearing `JsValue` variants and direct prototype,
   closure, parent, binding, and metadata references to `JsHeapHandle`, and
   delete stale `JsValue.Symbol` match arms because the operative value ABI has
   no Symbol variant.
3. Replace every numeric VM ownership property with a store-owned
   `JsTypedEdge`; preserve proven non-VM scalar IDs as numbers.
4. Migrate interpreter root tables, timers, Promise/async records, streams,
   iterators, WASM tables, runtime returns, DOM records, listener registrations,
   and event executors.
5. Introduce the exact-key external-root retain/release table.
6. Enable resolution generation checks everywhere.
7. Only after the static inventory contains no raw reusable VM IDs, enable
   sweep/free-list reuse and collection at the existing outer host safe point.

There is no mixed SBR-style compatibility phase for production VM references.
Any raw-ID path keeps reclamation disabled.

## Root and edge matrix

| Owner | Strong roots/edges | Release boundary |
|---|---|---|
| Call frame | environment, receiver, arguments, locals, return, thrown | frame pop after safe-point snapshot |
| Closure | function to closure environment | function reclamation |
| Timer | callback, arguments, handle object | cancel/fire plus outer host turn |
| Promise/async | task, handlers, registrations, request/response values | settle/cancel/drain |
| Stream | source, pending destination, queued values | close/cancel/drain |
| Iterator | source and current retained value | exhaustion/drop |
| WASM | module, imports, exports, function/body metadata | module/runtime disposal |
| DOM | window/document/body/elements/styles | document replacement/close |
| Listener/event | target, callback, frozen path, Event and arguments | unregister/dispatch completion |
| Host return | exact external owner key and typed edge | exact-key release |

Function-indexed native/bound/class/WASM metadata remains weak-keyed: a live
function key exposes its typed values; a dead key causes lockstep row removal.

## Mark and sweep

At the outermost safe point, freeze all interpreter and browser roots, then:

1. Validate each root handle generation and enqueue its typed store once.
2. Drain iterative object/function/environment queues.
3. Follow maintained typed adjacency exactly once per marked owner.
4. Remove dead weak-keyed metadata.
5. Sweep unmarked properties and slots in lockstep.
6. Advance generations, clear payloads, update O(1) counters, then publish free
   slots.
7. Resume the host only after invariants pass.

Collection remains inhibited during evaluation, native calls, recursive event
dispatch, timer/microtask drains, exception unwind, and listener mutation.

## O(1) counter contract

Allocation and release must not call `live_count()` or scan liveness/property
arrays. Each store maintains current `live`, `slot_capacity`,
`allocated_total`, `reclaimed_total`, `live_high_water`, and free-list length
by constant-time updates. Diagnostic counters include:

- `allocation_scan_count` (must remain `0`);
- `mark_visit_count`;
- `typed_edge_visit_count`;
- `stale_handle_reject_count`;
- `external_root_entry_count` and `external_root_retain_count`.

For identical fixtures, N is exactly `128`, 2N is exactly `256`, and the
frozen-root allowance is exactly `32`. Allocation scans remain zero and
`visits_2n <= 2 * visits_n + 32`. A focused 1,000-cycle run must keep live
roots and slot capacity bounded. The selected 10,000-cycle and RSS/pause
measurements are separately planned external production gates; the unit SSpec
does not tag or claim them.

## Error behavior

- Stale retain: typed error; no root or count mutation.
- Stale resolve: typed error/no value; no payload access or mutation.
- Stale mark: typed error and no enqueue; only diagnostic reject count changes.
- Stale release: typed error; no root, count, or occupant mutation.
- Invalid slot: the same fail-closed operation matrix applies.
- Unknown edge kind: fail closed before marking or sweep.
- Unknown handle store kind: fail closed before resolution or enqueue.
- Missing external root key: stale/foreign release error; no count change.
- Retain-count underflow: invariant failure; collection remains disabled.
- Generation exhaustion: retire slot; never wrap or alias.
- Raw numeric ownership found: static gate failure; sweep remains disabled.
- Counter or parallel-array mismatch: abort collection before slot reuse.

## SSpec handoff

The first RED contract is
`test/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.spl`, mirrored
at `doc/06_spec/01_unit/lib/nogc_sync_mut/js/engine/js_vm_reclamation_spec.md`.
Its exact steps and helpers are frozen in the agent and system-test plans.
`expect_gc_ownership_invariants` fails explicitly until production behavior
exists. The existing `common/js` lexical-parent spec remains prerequisite
evidence only and is not rewritten as collector evidence.
