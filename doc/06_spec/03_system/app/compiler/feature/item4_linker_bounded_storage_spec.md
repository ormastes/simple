# Checked spill transaction execution

Authority: `test/03_system/app/compiler/feature/item4_linker_bounded_storage_spec.spl`.
Requirements: ITEM4-REQ-007, 009. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Stage a real binary file using retained handles and bounded IO windows.
2. Reserve logical space for spill frames and the simultaneous private output;
   check exact quota boundaries and arithmetic overflow before staging.
3. Replay checked frame offsets, lengths and CRCs into private output and verify
   the published bytes against the original file.
4. Corrupt or truncate frames, cancel work, and collide with an existing output;
   require a failure that preserves the existing destination.
5. Force cleanup failure after successful publication. Require a committed
   outcome with cleanup pending, reject republishing, and retry cleanup after
   removing the task-owned blocker.

Scratch accounting is logical bytes, not whole-job memory or filesystem
allocation. Full bounded linker admission remains unsupported.

