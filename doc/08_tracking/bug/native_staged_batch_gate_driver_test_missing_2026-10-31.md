# Staged codegen: no driver-level test or measurement for the batch-local gate

Status: OPEN
Date: 2026-10-31

PR #5615 keeps a lowering failure local to its batch, but its spec case covers only
`record_batch_lowering_v1`; it still passes if the lowering loop's flag, OR or reset is removed.
Object output is unmeasured: the fix needs a stage2 built from it, and none has been built.

Fixture note: `undefined_thing_xyz` and bare `eprint` in a small project both fail at HIR, not MIR,
so neither reaches this gate. The test needs a module that passes HIR and fails MIR.

Unblock: add a driver-level test with a failed module in a middle batch and in the tail. Assert that
later batches emit objects, the failed batch emits none, and the build errors without linking.
