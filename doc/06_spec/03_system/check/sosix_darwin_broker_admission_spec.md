# Darwin direct-child admission — native evidence

Executable spec: `test/03_system/check/sosix_darwin_broker_admission_spec.spl`.
Native driver: `scripts/check/check-sosix-darwin-broker-admission.shs`.

| Adversarial action | Required evidence |
| --- | --- |
| Inject a dylib into ordinary unbound helper startup | Constructor marker appears before main (RED control) |
| Inherit hostile dyld/malloc/application variables and an open descriptor | Bound helper constructor sees empty environment and only standard descriptors |
| Connect an unrelated same-UID peer | Reject before an admission byte |
| Change expected child PID version or CDHash | Reject admission |
| Replace endpoint with a same-UID rogue listener | Helper emits zero protocol bytes |
| Keep the live helper waiting for admission | Read deadline expires; gate stays closed |
| Stop the closed helper and cancel | Bounded direct-child reap receipt |
| Saturate a listener queue | Connect returns within its deadline |
| Lose child ownership (`ECHILD`) | Return failure without signalling |
| Supply wrong spawn CDHash | No helper constructor entry |
| Supply cooperative/unbound image | Reject admission with `ENOTSUP` |

Native TDD: missing admission header initially failed compilation. After
implementation the native controls passed. Security review added bounded connect,
a shared admission deadline, and closed-gate cancellation evidence. A backlog-zero
fixture assumption failed and was corrected to backlog one; all native controls
then passed.

The wrong-hash control requires natural child termination without sending a
signal first, so cleanup cannot hide an ignored constraint. A disposable mutation
that omitted the AMFI attachment failed this natural-termination assertion.

Final reviewed validation: PASS, one SSpec file and one example (2026-10-29).
The modern SSpec executes the native driver and checks every evidence marker.
Validation uses the existing user-authorized P1 diagnostic binary in interpreter
mode, with no cache/database/session daemon, sequential execution, and
`--assert-ran`. No compiler or Phase 2 rebuild is performed.

No workload is executed. No disjoint coalition, descendant receipt, or generic
V4 capability is claimed. Launchd's original-job admission gap remains explicit;
this direct-child mechanism avoids trusting that label namespace.
