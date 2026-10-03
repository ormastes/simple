# Checked spill transaction execution

Authority: `test/03_system/app/compiler/feature/item4_linker_bounded_storage_spec.spl`.
Requirements: ITEM4-REQ-007, 009. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Admit a real scratch directory and reject regular-file, missing and NUL
   parents through the native retained-file owner, without a runtime-only probe.
2. Create a real Linux directory symlink or Windows junction. Reject it as the
   scratch parent, including a trailing separator; remove only the alias and
   prove its real target survives. The platform alias-creation command is an
   explicit fixture prerequisite, not a skipped failure.
3. Stage a real binary file using retained handles and bounded IO windows.
4. Reserve logical space for spill frames and the simultaneous private output;
   check exact quota boundaries and arithmetic overflow before staging.
5. Replay checked frame offsets, lengths and CRCs into private output and verify
   the published bytes against the original file.
6. Corrupt or truncate frames, cancel work, and collide with an existing output;
   require a failure that preserves the existing destination.
7. Force cleanup failure after successful publication. Require a committed
   outcome with cleanup pending, reject republishing, and retry cleanup after
   removing the task-owned blocker.

Scratch accounting is logical bytes, not whole-job memory or filesystem
allocation. Full bounded linker admission remains unsupported.
