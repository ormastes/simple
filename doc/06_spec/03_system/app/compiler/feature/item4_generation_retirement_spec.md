# Generic generation retirement specification

**UNRUN — authored manual; canonical generation and runtime execution pending.**

Source: `test/03_system/app/compiler/feature/item4_generation_retirement_spec.spl`.
Traceability: ITEM4-REQ-010 / PACK-POS006 generic shutdown prerequisite.

1. Fill a one-generation, one-pin table. Confirm another publication and pin
   fail for capacity, then retire the active generation without a replacement.
   Check identity, digest, revision, retired state, and retained pin count.
   Collection must fail while pinned and succeed after release.
2. Publish and pin an older generation, then publish a successor. Reject
   retirement of the old handle and forged successor handles. Check views and
   active pin acquisition, then successfully roll back to prove rejection did
   not erase rollback authority. Release pins and clean up both generations.
3. Retire a successor, reject repeated retirement and rollback, and confirm no
   active pin is available. Collect both generations, publish into the reused
   slot, and verify its new epoch survives an attempted retirement using the
   stale handle. Retire and collect the replacement.
4. Reject retirement and active pin acquisition on a zero-capacity table;
   verify capacities remain zero.

All transitions call the production table; no simulated success is used.
This manual does not establish mapped-provider unload, CLI wiring, trusted
manifest admission, full compiler acceptance, coverage, or performance.
