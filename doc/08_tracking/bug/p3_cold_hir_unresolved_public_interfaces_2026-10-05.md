# Phase 3 cold HIR public interfaces remain unresolved

Status: OPEN. One source workaround; diagnostic improvement. Native validation UNRUN.

The frozen 916be Phase 3 streaming packet completed all 1142 HIR shards and
validation with zero errors, then exited 1 during cold receipt creation. It did
not reproduce the earlier retained-HIR access violation. The owner build log
SHA-256 is `04bb63ef886be4b32101ad1019337bdf9c52206a8c95de269edcd177a47b1677`.

All four errors were `cold-hir-abi-unresolved:unresolved-inference:0:0`:

- compiler.common.cache_contract.virtual_source_store_v1
- lib.nogc_sync_mut.src.map
- lib.nogc_sync_mut.src.hash
- compiler.backend.verify.allocator_symbol_scan

Source-proven path: `lower_hir_const_decl` recognizes primitive literal types
but uses `Infer(0,0)` for an unannotated array initializer. The allocator module
exports `FORBIDDEN_ALLOCATOR_SYMBOLS` with such an initializer. Annotating its
existing text array preserves its contents and semantics while avoiding that
fallback. This is a workaround; general constant inference remains unfixed.

The other three declarations are not yet identified. Generic/default and flat
type conversion paths are investigation candidates, not proven causes. The ABI
encoder now attaches the containing public declaration kind/name to its first
error. Valid encoded payload bytes remain unchanged; unresolved interfaces are
still rejected. No inference is changed to Any and no module is omitted.

There is no dedicated safe cold-receipt bypass found. Existing warm compatibility
markers are authority inputs, not a diagnostic bypass; manufacturing them would
misrepresent the build. No such workaround was applied.

Regression specs exercise rejection and exact constant attribution, a resolved
text-array ABI, and exclusion of private inference without changing public ABI.
These Simple specs are UNRUN pending a suitable self-hosted test producer.
The current producer can use the explicit array annotation. Improved diagnostic
messages require the coordinated compiler rebuild; do not restart live packets.

Memory/performance review: the annotation has no new runtime allocation. Error
context adds one short string only on failure and stops encoding after the first
invalid declaration. Valid encoding traversal/payload remains unchanged. Runtime
RSS and latency are unmeasured. Full closure verification and the other three
root causes remain outstanding.
