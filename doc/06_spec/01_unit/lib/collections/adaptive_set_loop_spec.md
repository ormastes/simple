# Completed adaptive set loops

Requirement: REQ-PSC-003. Executable scenarios:
[adaptive_set_loop_spec.spl](../../../../../test/01_unit/lib/collections/adaptive_set_loop_spec.spl).
Status: authored manual; Simple scenarios UNRUN. Native capture-owner tests
passed independently and do not establish execution of these scenarios.

1. Visit a set inserted in unsorted order under linear, hash and ordered
   representations. Continue visits `a`, `b`, `c` once and reports three trips.
2. Return Break on `b`. The trace ends at `b` and reports two trips.
3. Return an error on `b`. Preserve the two callback effects and return the error
   without a completed observation.
4. Visit an empty set. Do not invoke the callback; report known zero trips.
5. Reject missing site or target identity before invoking callbacks.
6. Reject a mismatch between stored size and snapshot cardinality before callbacks.
7. Reject duplicate snapshot keys before callbacks.
8. Capture a completed break and a failed invocation at distinct stable sites.
   The break metric is two; the failed invocation's loop metric is absent.
9. Capture an empty loop and require a zero metric, distinct from absence.
10. Make capture reject an invalid site. The completed loop and callback trace
    remain successful; profile finish reports failure.

The API uses a validated snapshot and copies identities before callbacks.
Counts represent actual callback entries. They do not substitute for general
compiler loop instrumentation, join metrics, or cross-backend acceptance.
