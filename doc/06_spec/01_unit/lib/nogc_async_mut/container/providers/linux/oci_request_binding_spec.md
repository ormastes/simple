# OCI payload binding and legacy migration

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_request_binding_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. This source mirror is not runtime-generated
evidence. The admitted self-hosted runtime is unavailable.

The following 14 scenarios are authored acceptance checks. Expected results
come from their executable assertions, not from an observed run.

1. Persists a fresh request before create and reopens the same bound identity.
2. Does not let an accessor replace cached immutable operation authority.
3. Never resurrects a scripted bound tombstone by persisting prepared intent.
4. Allows identical prepare and create replay with one exact native create.
5. Publishes V2 for exact scripted create and retains its native identity on disk.
6. Rejects changed command args image resources and operation before cached success.
7. Rejects NUL before logical state reservation or executor use.
8. Recovers matching durable V2 while refusing changed payload after restart.
9. Does not overwrite corrupt noncanonical or foreign records.
10. Refuses a dangling journal link before exact scripted create can execute.
11. Checks disk against stale prepared memory and keeps destroyed tombstones.
12. Refuses legacy create and start but reconciles exact identity without V2 promotion.
13. Rejects unqualified legacy operands before every reconciliation executor.
14. Rejects option-like operands at every native-id command builder.

Provider fixtures use real owner methods and exact argv matching. Optional real
journal persistence exercises canonical publication and format-preserving V1
cleanup; the executor-entry counter distinguishes attempted effects from matched
fixture consumption. The retained-request codec is data-only and does not grant
authority to use schema fields whose runtime effects remain refused.

No native container success, timing/RSS measurement, SPipe execution, docgen
PASS, or power-loss durability experiment is claimed. See
`doc/05_design/oci_request_binding_admission.md` for provenance, migration policy,
trusted-directory limits, and remaining verification.

The changed-payload and V1 cleanup scenarios invoke the shared builtin-assert
checks in `test/fixtures/orchestration/oci_binding_admission_fixture.spl`. The
matching tiny direct probe remains BLOCKED / UNEXECUTED because the available
producer has a known unchanged secure-memory dependency failure. No build was
attempted, and the shared source is not additional executed evidence.
