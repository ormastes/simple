# Failed exclusive pin creation deletes another reader lease

Status: source reviewed, waiting_verify; runtime verification UNRUN. Severity: P1.

At reviewed directory prerequisite fe67a12, shared_generation_pin_current_owned_v1
combined failed file_create_excl with fsync failures and unconditionally deleted
the lease path. A duplicate lease ID therefore removed an already active reader's
lease, allowing later GC to lose its protection. Other exclusive-create failures
could also delete a path the current operation did not create.

The repair returns immediately on create failure and only cleans up leases after
successful exclusive creation. The generic lease-create-failed reason does not
claim errno information unavailable from the runtime API. The current owner is
shared_generation_store, reused by the directory TLDR store/gate.

Authored real-filesystem regression in shared_generation_publication_spec.spl
creates one pin, collides a second owner on the same ID, verifies the first live
lease remains, then releases it. Execution UNRUN; source review acceptance is not
runtime proof. Full directory gate authority/codec integration is separate.
