# smux primary V4 lifecycle guards

Source: `test/01_unit/os/apps/smux/runtime_primary_lifecycle_guards_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion, not generated execution evidence.

Six scenarios exercise production-used guards: unchanged adoption and all
cleanup-state transitions; refusal of each changed adoption field; exact signed
helper journal admission permitting retry only while admitted, refusing before
admission, changed envelopes, and executing replay. The journal fixture retains
capacity charges and releases its actual journal owner on cleanup.

Two scenarios exercise the actual internal pending-marker functions used by
both bind and recovery lanes. With both domains carrying the same textual UID,
resolving primary preserves output uncertainty and resolving output preserves
primary uncertainty. Duplicate adds/resolutions preserve the outstanding other
domain; only resolving its own domain empties the list. No archive or native
recovery is performed by these metadata-only regression scenarios.

The final metadata scenario exercises the shared pruning/inspection predicate:
a fully released same-UID tombstone permits continuation, unresolved status or
any retained/pending metadata blocks it, and another UID does not conflict.
This asserts the actual guard used by both domains; it does not execute the
subsequent archive/native recovery operation.

Adoption inputs are metadata only, never fabricated live primary sessions. The
signed-data/admission fixture does not execute the complete failed-begin server
transaction. Native adoption, stale-session publication, sole-reader IO,
cleanup, and Host ACK release remain **NOT_COVERED** by these guard tests.
