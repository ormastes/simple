# JavaScript VM Generation-Safe Ownership

Status: **PROPOSED / RED — fail-fast design contract only.**

This manual freezes the ownership ABI and evidence flow. The checker
intentionally fails because no collector implementation or admitted runtime
evidence exists. It does not claim GC, RSS, pause, lifecycle, or browser PASS.
The 10,000-cycle requirement belongs to a planned external production gate,
not this executable contract.

## Retain independent escaped values

Create two independent external owners for the same escaped Event, object, and
closure. The sequence `retain A, retain A, retain B, release A, release A,
release B` must yield A counts `[0,1,2,2,1,0,0]` and B counts
`[0,0,0,1,1,1,0]` through 1,000 cycles.

## Trace typed closure roots

Trace object, function, environment, closure, timer, Promise, stream, iterator,
WASM module/import/export/function, DOM node/style, listener target/callback,
pending event, and temporary host-return edges only through `JsTypedEdge`.
`JsTypedEdge.kind` remains semantic while `handle.store_kind` selects exactly
one object, function, or environment store. The operative `JsValue` has no
Symbol variant; migration deletes stale `JsValue.Symbol` match arms and does
not add a speculative Symbol store.
Ordinary numeric values and author-visible property names are negative
controls.

## Reject stale releases after reuse

Reclaim one lifetime, reuse its slot at a new generation, then submit the old
owner key. Stale retain, resolve, mark, and release must reject respectively
without root mutation, value access, enqueue, or occupant/count mutation.

## Reclaim without allocation scans

Across N=`128`, 2N=`256`, frozen-root allowance=`32`, and 1,000 focused
cycles, allocation scans remain zero, live counters update in O(1), and
`visits_2n <= 2 * visits_n + 32`. The separate external production
10,000-cycle, 60-minute RSS, and pause gates remain RED.

<details>
<summary>Complete executable SSpec</summary>

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-017
# @req REQ-WEB-BROWSER-018
# @req NFR-WEB-BROWSER-007
# @req NFR-WEB-BROWSER-008
# @req NFR-WEB-BROWSER-015
# @req NFR-WEB-BROWSER-016

use std.spec.*

"""
Fail-fast design contract for generation-safe JavaScript VM ownership.

This spec is intentionally RED until the selected nogc_sync_mut engine exposes
the frozen JsHeapHandle, JsExternalRootKey, and JsTypedEdge ABI. It is not
runtime, GC-pause, RSS, or production-browser evidence.
The external production gate, not this contract, owns 10,000-cycle evidence.
"""

class GcOwnershipContractFixture:
    case_name: text
    cycle_count: i64
    n: i64
    two_n: i64
    frozen_root_allowance: i64
    expected_allocation_scan_count: i64
    required_interfaces: [text]
    required_store_kinds: [text]
    required_migration_guards: [text]
    required_edge_kinds: [text]
    ownership_operations: [text]
    same_key_retain_count_oracle: [i64]
    independent_key_retain_count_oracle: [i64]
    stale_operation_oracle: [text]

fn make_gc_ownership_fixture(
    case_name: text, cycle_count: i64
) -> GcOwnershipContractFixture:
    GcOwnershipContractFixture(
        case_name: case_name,
        cycle_count: cycle_count,
        n: 128,
        two_n: 256,
        frozen_root_allowance: 32,
        expected_allocation_scan_count: 0,
        required_interfaces: [
            "JsHeapHandle(store_kind,slot:i64,generation:i64)",
            "JsExternalRootKey(handle,owner_kind,owner_id)",
            "JsTypedEdge(kind,handle)"
        ],
        required_store_kinds: ["object", "function", "environment"],
        required_migration_guards: [
            "edge kind is semantic; handle store_kind selects storage",
            "delete stale JsValue.Symbol match arms; do not add Symbol"
        ],
        required_edge_kinds: [
            "object",
            "function",
            "environment",
            "closure_environment",
            "timer_callback",
            "timer_argument",
            "promise_task",
            "promise_handler",
            "promise_registration",
            "stream_source",
            "stream_destination",
            "iterator_source",
            "wasm_module",
            "wasm_import",
            "wasm_export",
            "wasm_function",
            "dom_node",
            "dom_style",
            "listener_target",
            "listener_callback",
            "pending_event",
            "temporary_host_return"
        ],
        ownership_operations: [
            "retain_a",
            "retain_a",
            "retain_b",
            "release_a",
            "release_a",
            "release_b"
        ],
        same_key_retain_count_oracle: [0, 1, 2, 2, 1, 0, 0],
        independent_key_retain_count_oracle: [0, 0, 0, 1, 1, 1, 0],
        stale_operation_oracle: [
            "retain:reject:no_mutation",
            "resolve:reject:no_value",
            "mark:reject:not_enqueued",
            "release:reject:no_mutation"
        ]
    )

fn expect_gc_ownership_invariants(fixture: GcOwnershipContractFixture):
    fail("RED: generation-safe JS VM reclamation is not implemented")

describe "JavaScript VM generation-safe ownership":
    describe "REQ-WEB-BROWSER-018: independent escaped ownership":
        it "should retain equal escaped values for independent owners":
            step("Retain independent escaped values")
            val fixture = make_gc_ownership_fixture(
                "independent host, DOM, listener, Event, object, and closure owners",
                1000
            )
            expect_gc_ownership_invariants(fixture)

    describe "REQ-WEB-BROWSER-017: complete typed graph":
        it "should trace closure and host families without numeric guessing":
            step("Trace typed closure roots")
            val fixture = make_gc_ownership_fixture(
                "timers, promises, streams, iterators, WASM, DOM, and listeners",
                1000
            )
            expect_gc_ownership_invariants(fixture)

    describe "REQ-WEB-BROWSER-018: generation-safe reuse":
        it "should reject a stale owner release after its slot is reused":
            step("Reject stale releases after reuse")
            val fixture = make_gc_ownership_fixture(
                "old generation release cannot affect the new occupant",
                1000
            )
            expect_gc_ownership_invariants(fixture)

    describe "NFR-WEB-BROWSER-015/016: bounded linear work":
        it "should preserve O(1) allocation counters across N, 2N, and cycles":
            step("Reclaim without allocation scans")
            val fixture = make_gc_ownership_fixture(
                "zero allocation scans and linear typed mark visits",
                1000
            )
            expect_gc_ownership_invariants(fixture)
```

</details>

## Traceability

| Requirement | Contract contribution | Status |
|---|---|---|
| REQ-WEB-BROWSER-017 | Typed complete roots and bounded observable work | RED |
| REQ-WEB-BROWSER-018 | Independent ownership and stale-release rejection | RED |
| NFR-WEB-BROWSER-006/014 | Planned external production 10,000-cycle gate only | RED / not tagged by unit contract |
| NFR-WEB-BROWSER-007/008 | Safe-point/lifecycle obligations | RED |
| NFR-WEB-BROWSER-015/016 | O(1) allocation and N/2N visit counters | RED |
