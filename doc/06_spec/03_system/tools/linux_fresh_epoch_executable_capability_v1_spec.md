# Actual refusal: privilege xattr on the retained provider or broker

Source: `test/03_system/tools/linux_fresh_epoch_executable_capability_v1_spec.spl`.
Status: AUTHORED_NOT_RUN. No native qualification, docgen or compiler run.

Use a SEPARATE disposable already provisioned supported fresh-epoch Host fixture.
The administrator adds a real nonempty security.capability xattr to the pinned provider or broker executable without changing its content digest. The executable is never run by this spec.
The graph/run roots stay genuinely empty and every other supported topology
prerequisite must hold. This fixture is distinct from the positive fixture and
other negative fixtures; the spec does not install or alter host privileges.

1. **Require the real installed service profile before the native negative observation.**
   Require the actual fixed root-owned profile, current dedicated UID and genuine
   machine reader. Missing prerequisites fail; they never satisfy the negative.
2. **Observe privilege xattr on the retained provider or broker through the real factory; an unrelated failure cannot pass.**
   Actual production preparation must return cleanup-required with exactly
   `fresh-epoch-native-executable-file-capability-present`. Ready or a different/earlier error fails. Require actual cleanup
   closure and current refusal; retained arrays keep unresolved owners reachable.

Trace: REQ-LINUX-FRESH-EPOCH-006. This is authored real-fixture coverage only;
no result or native fault/enforcement coverage is claimed. See the lower design
for trust boundaries and the separate actual upper admission/workload fixture.
