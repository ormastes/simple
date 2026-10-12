# Actual transient scope state for borrowed capture preconditions

Date: 2026-10-12. Status: implementation and guards authored; qualification pending.

Bounded HIR/archive capture needs to reject an inactive or paused caller context
before collecting values. A caller-supplied Boolean cannot establish this
runtime precondition, and calling begin to probe it can acquire or interfere
with a scope. The previous public begin/pause/end API had no read-only query.

`rt_transient_array_scope_state_v1() -> i64` returns:

- `0`: inactive in the current runtime execution context;
- `1`: active and unpaused;
- `2`: active and paused.

The typed alias is
`std.nogc_sync_mut.sffi.runtime.transient_array_scope_state_v1() -> i64`.
Borrowed capture requires the exact value `1` before collection. The query
does not open, pause, close or steal a scope. It provides no lease, creator
identity, authorization token or ownership transfer; the caller's existing
borrowed ownership contract still applies.

## Actual owner implementations

C reads `runtime_native.c`'s existing TLS active/paused fields and verifies the
actual atomic owner against the calling thread's internal scope token. A
foreign thread therefore observes inactive even while a global C scope owner
is active. The getter does not modify fields, registries or atomic ownership.

Rust reads its own `TRANSIENT_HEAP_SCOPE` TLS cell. No C query is forwarded.
Another Rust thread has its own inactive context and can create its own scope
through the existing real thread-local raw allocator API. Heap handles and
scope state are interpreted by the selected owner, never another runtime's
similarly named globals.

Simple reads `core_memory.spl`'s actual active/paused globals shared by its
begin/pause/end operations. This owner documents single-thread execution;
the implementation does not claim TLS or multi-thread qualification.

The core-C runtime-native object admission now requires the defined query
and all three lifecycle exports together. Existing source/header/tool-keyed
cache admission still applies. A stale C object missing the query must not
resolve it from Simple backfill globals while begin/end use the C scope.
Rebuild and admit changed runtime identities through the normal pipeline.

## Actual lifecycle guards

`test/01_unit/runtime/transient_scope_state_contract_test.c` exercises inactive
query, failed inactive pause/end, begin, repeated active query, refused nested
begin without state change, pause, repeated paused query, refused paused nested
begin, end, repeated inactive query, and a second complete scope. Its default
core-C build has 18 numbered positive guards, including foreign-thread calls
while the owner is active and paused. A foreign C begin/pause/end must refuse
without changing either thread's state.

For a genuine Simple owner, compile the same C guard with
`SIMPLE_SCOPE_STATE_SINGLE_THREAD`; it executes the 16 non-thread guards.
Link the actual `core_memory` and its real array/dict/enum/closure/string/Float
provider closure and selected host primitives. Run the selected module
initializers normally. No C runtime-native scope provider or test stub may
satisfy those APIs. This compile mode expressly excludes TLS qualification.

`src/compiler_rust/runtime/src/value/transient_scope_state_tests.rs` contains
two actual Rust-owner tests: complete lifecycle/state preservation and thread
isolation. The latter creates an independent scope on the second thread while
the first remains active or paused, then proves the first state unchanged.

Retain actual source/object hashes, build/export receipts and link ownership
for the query and lifecycle functions before and after linking. Require
terminal exit zero for the selected C/Simple executable and actual passing
Rust tests. Native jobs have not run for this patch; all guards are unexecuted.

Close this prerequisite only with those runtime receipts and the dependent
borrowed archive/HIR capture refusal and active-context cases. A source-level
symbol census or caller Boolean does not substitute for runtime evidence.
