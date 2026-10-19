# Aspect lifecycle reclamation scenarios

Requirements: P4/P5 generic dynamic lifetime/resource closure, AD-02 and retained
REQ-L06-A06/A07. Source tests were ported before production. Status: UNRUN;
pre-fix RED is source-predicted (new APIs absent), not an execution result.

## Common lifecycle API

Executable: `test/01_unit/lib/aspect_dynload_callback_quiescence_spec.spl`.

1. Complete 1025 sequential create, callback, unload, completion and reclaim
   cycles. One slot is reused, each incarnation increases, and stale snapshots
   refuse immediately after reclaim.
2. Reuse the exact slot with identical facet/generation/lease ID. Copied old
   handles and leases must not begin, complete, advance, unload or reclaim the
   new owner; its live count remains one until its real lease completes.
3. Refuse reclaim for active ownership and quiescing continuation/device-fence
   ownership. Drain both actual leases, then permit reclaim exactly once.
4. Check negative, zero, max-minus-one and max incarnation transitions without
   manufacturing billions of live objects or allowing signed wraparound.

## Loader and physical ownership

Executable: `test/01_unit/compiler/loader/aspect_final_unpin_v3_authority_spec.spl`.

5. Build the canonical admitted startup fixture and map it through the real
   owners. Perform 1025 public bound acquisitions/releases without increasing
   simultaneous pins or mapping count; finish via one acknowledged final release.
6. Keep a retired product slot reserved until final completion. Reuse it with a
   new live callback, then replay the old public final receipt. The callback and
   incarnation remain intact and no native release is dispatched again.
7. A executes real internal preparation/native dispatch. B uses public retry to
   recover and finish that retained attempt. Reuse the slot, then resume A through
   the same production continuation. Both results remain terminal; the fresh
   callback is untouched and later public replay dispatches nothing.

The seventh case deterministically schedules production boundaries; it is not
an OS-thread concurrency proof. It never sets private lifecycle or final-row
state. Common direct API cases use their single-owner contract; product cases
use the actual lifecycle gate. The inherited real mapped fixture and counters
are not fake providers, but their runtime behavior is still unqualified here.
The landed AD-01 guard and its partial-drain/exact-once assertions are unchanged.
No performance, generic executable-body admission or full resource PASS is claimed.
