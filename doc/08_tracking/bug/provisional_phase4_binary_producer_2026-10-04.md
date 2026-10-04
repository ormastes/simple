# Provisional Phase 4 binaries reused the Phase 2 producer

The diagnostic scheduler labeled binary tasks Phase 4 while passing the
original provisional producer to every binary manifest. Those executables did
not demonstrate the required Phase 3-to-Phase 4 compiler lineage.

Phase 4 binary tasks now select their own backend's published Phase 3 bootstrap
compiler. Before creating the task manifest, the runner verifies its prior
manager receipt and output digest, then requires an actual hello compilation
and execution with that compiler. The manifest pins the selected executable.
The completion journal records its digest and hello receipt digest; replay
verification checks the retained producer and hello evidence. Missing or
changed predecessor evidence blocks that dependent binary task, without
substituting the original producer. Other independent tasks continue.

The scheduler attempts next-generation binaries immediately after the Phase 3
bootstrap binary, before broader module inventory qualification. Both backend
lanes retain their own caches and journals. All inventories still run.

Validation: focused shell tests cover initial producer selection, verified
next-generation selection, absent predecessor, cross-backend reuse, changed
hello evidence, failed manager verification, and changed producer bytes.
The scheduler test verifies concurrent backend dispatch, failure collection,
and next-generation scheduling before Phase 3 inventory qualification.
Shell syntax and whitespace checks pass.

Full bootstrap execution remains pending. Module-index/group provenance still
uses the provisional compiled authority and is not promoted by this binary
handoff. Run-level Phase 3/4 status remains INCOMPLETE and tool evidence remains
unproven until canonical qualification. This change does not admit an RC.
