# Linux OCI provider contract

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. This source mirror is not runtime-generated
evidence. The admitted self-hosted runtime is unavailable.

The following 26 scenarios are authored acceptance checks. Expected results
come from their executable assertions, not from an observed run.

1. Assembles Podman argv without a shell and keeps the default engine explicit.
2. Fails closed when any rootless launch prerequisite is absent.
3. Rejects missing create policy instead of silently launching unbounded.
4. Rejects CPU quota multiplication overflow before argv construction.
5. Classifies only engine-specific definitive absence as not found.
6. Fails closed for non-Linux, invalid identity, and unsafe input.
7. Keeps a blocked host lane prepared but never advances it on a failed live prerequisite.
8. Runs create, start, inspect, wait, stop, and destroy through exact scripted argv.
9. Recovers only a matching operation, generation, native identity, and boot.
10. Reloads the pre-create intent journal before native recovery.
11. Honors a durable destroyed tombstone after restart without native recreation.
12. Rejects destroyed tombstones from another provider identity.
13. Inspects a timed out attempt before allowing a create retry.
14. Retries create after definitive absence but preserves transient inspect failure.
15. Never recreates a previously created workload after native absence.
16. Checks inspect after a create error before reporting failure.
17. Uses the pure lifecycle oracle for force and idempotency decisions.
18. Does not retain an intent whose durable journal write failed.
19. Bounds active state and intent storage without a growing lookup scan.
20. Keeps destroy idempotent when only the durable destroyed intent remains.
21. Reads a durable destroyed tombstone even when the intent cache is full.
22. Recovers an uncached durable active intent through a full non-evictable cache.
23. Reconciles a durable destroyed intent through a full non-evictable cache.
24. Bounds retained scripted fixture records.
25. Compacts old destroyed pairs while preserving active state.
26. Rejects recovery state insertion at capacity without growing storage.

Provider fixtures use real owner methods and exact argv matching. Optional real
journal persistence exercises canonical publication and format-preserving V1
cleanup; the executor-entry counter distinguishes attempted effects from matched
fixture consumption. The retained-request codec is data-only and does not grant
authority to use schema fields whose runtime effects remain refused.

No native container success, timing/RSS measurement, SPipe execution, docgen
PASS, or power-loss durability experiment is claimed. See
`doc/05_design/oci_request_binding_admission.md` for provenance, migration policy,
trusted-directory limits, and remaining verification.
