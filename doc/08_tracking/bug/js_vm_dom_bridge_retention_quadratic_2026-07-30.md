# JS VM DOM bridge retention is frame-linear and property-scan quadratic
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Open. No implementation, executable spec, or production receipt is merged.
The diagnosis and bounded tracing-GC design passed high-capability review;
Root Codex owns any future implementation merge.

## Reproducer and impact

A JavaScript `requestAnimationFrame` loop that replaces
`document.body.innerHTML` retains one old DOM bridge generation per frame.
The current minimal replacement has implicit `html`, `head`, and `div` nodes:
the focused test encodes `replacement_object_count = 7`, while production
allocation logic proves **1 + 2*3 = 7** new VM objects per replacement (one
element-list object plus three element/style pairs).

The chain is:

1. `BrowserSession.advance_time` drains the rAF callback and flushes runtime
   side effects.
2. `JsInterpreter._publish_host_body_mutation` admits a new bridge generation,
   creates its objects, and adds its object/byte totals to cumulative retained
   counters.
3. Browser-session synchronization adopts that bridge for the new DOM.

Neither retained counter decreases during a document lifetime. A minimal
replacement accepts frame 4,681 at 32,767 retained objects, then rejects frame
4,682 because it would require 32,774 (about 78 seconds at 60 Hz). Later DOM
updates are silently ignored to preserve the old body.

The same path is time-superlinear. `JsInterpreter.set_object_property` scans
the monotonically growing property arrays before it writes. Existing keys
update in place, but each fresh bridge generation introduces fresh object IDs
and keys, so its writes scan an ever-larger store: retained property work is
**Theta(frames^2)** before the cap is reached.

## Exact owners

- `src/lib/gc_async_mut/web/browser_session_runtime.spl`: rAF drain and bridge
  synchronization.
- `src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl`: host body
  mutation admission, bridge allocation, and cumulative counters.
- `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl` and
  `interpreter_object.spl`: monotonically growing object IDs and fresh-
  generation property storage; existing keys update in place, and the owning
  `JsInterpreter.set_object_property` performs the reverse property scan.

Navigation and `BrowserSession.close()` discard `runtime_state`, so they release
the whole document runtime. They do not fix a long-running page animation.
rAF timer handles retire correctly and CSS animation instances are reconciled;
neither is this defect.

## Unsafe shortcuts rejected

- Do not reset the retained counters: that removes the only admission bound and
  permits unbounded retention.
- Do not free or reuse a bridge generation by DOM generation alone: detached
  elements can escape into JavaScript and must remain distinct from replacement
  elements.
- Do not rebuild the whole runtime for every body mutation: it destroys globals,
  closures, listeners, timers, and rAF continuity.

## Required scoped prerequisite

This needs VM tracing reclamation, not a bridge-local delete. Add stable object
liveness metadata and sweepable property storage without remapping live IDs;
track environment parents/liveness and function records; then mark every
interpreter-owned `JsValue`/function/environment root: global bindings and
global values, call frames (including `this` and returns), `return_value`,
`thrown_value`, object/array properties, functions and closure environments,
host DOM roots, timer/async/promise work, listeners, prototypes, bound/native/
wasm caches, and Node require-cache values. Sweep only at a post-callback/
post-microtask safe point after a committed bridge replacement. Preserve every
marked detached element and callback identity. Existing byte/node admission
limits remain DoS bounds, but report current live counts rather than cumulative
allocation totals.

## RED SSpec and performance acceptance

Add a focused SSpec with these exact steps:

1. `Create bounded animation work` — a 256-frame rAF chain replaces one body
   child; retain the pre-replacement element and one callback/listener.
2. `Advance many frames` — advance deterministic 16 ms ticks and prove all 256
   callbacks ran, the retained detached element remains distinct/readable, and
   the current element/listener still works.
3. `Release navigation state` — navigate to a new document, then close.
4. `Verify retained counts and RSS/operation bounds` — live object/property
   counts plateau at the current bridge plus the explicitly retained detached
   element, callback, and listener roots; new-document counts start clean and
   close clears the runtime. A production perf companion runs N and 2N frames,
   records RSS delta for the NFR receipt (report-only until a selected numeric
   RSS threshold exists), and gates 2N elapsed time at no worse than 2.2x N.

Use live-object/live-property metrics, not monotonic `next_id`. The current
test that expects the cap to reject a second replacement is regression evidence
for this bug, not proof of lifecycle correctness.


## 2026-11-05 — quadratic property-scan half fixed on work/libbug-w6-jsbridge-20261105

Scope: only the time-superlinear property-scan half of this bug. The
frame-linear retention half (cumulative retained counters, no tracing
reclamation) is unchanged and still needs the scoped VM tracing
reclamation prerequisite above.

Root cause found on `origin/release/1.0.0`: the interpreter write path
(`JsInterpreter.set_object_property`) already used the (obj_id, key) slot
index, but `ObjectStore` still performed whole-store linear scans in
`set_property` (per write), `array_length` (per call, from for-of loops,
spread, array natives), `remove_property` (per call, from CSS style
writes), and `JsInterpreter.get_object_property_exact_key` (per require
cache lookup). Against a store that grows monotonically with retained
bridge generations, each operation scanned every stored slot:
Theta(total properties) per operation.

Fix: all four operations now resolve the object's slots through the
existing `obj_slot_index` (`object_slots`, synced on entry) and touch only
those slots. Whole-store scans remain only as counted fallbacks when the
index is provably out of sync (`ObjectStore.scan_ops`). Correctness
semantics are unchanged (first-match update for `set_property`,
max-index-derived length, all-matches removal, exact-key last-match).

Spec evidence: `test/01_unit/lib/nogc_sync_mut/js/engine/object_store_scan_bounds_spec.spl`
bounds property work by `scan_ops == 0` (deterministic under the
interpreter; no wall-clock gate): 1000 decoy slots from simulated prior
bridge generations, then writes/reads/array lengths/removals/array
creation on live objects must perform zero whole-store scans. RED before
the fix measured ~0.5-0.6M whole-store scan iterations for these trivial
workloads; GREEN after the fix is exactly 0. Pre-existing specs
(`object_store_slot_index_spec`, `interpreter_object_single_owner_spec`,
`promise_constructor_spec`, `regex_literal_replace_spec`,
`object_property_write_budget_spec` in both async-mut variants, and the
`test/01_unit/lib/js/` engine specs) pass identically before and after,
except baseline failures unrelated to this change
(`statement_dispatch_*`, `function_scope_chain_and_global_constructors`)
which fail identically with and without the fix.

Remaining: retention half (live-object plateau metrics, RSS receipt,
256-frame rAF SSpec) still owned by the VM tracing reclamation
prerequisite; `js_vm_reclamation_spec.spl` remains intentionally RED
until the frozen JsHeapHandle/JsExternalRootKey/JsTypedEdge ABI lands.
