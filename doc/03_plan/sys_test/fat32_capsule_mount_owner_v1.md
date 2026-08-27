# FAT32 capsule mount owner v1 test plan

- Mount a valid bounded FAT32 candidate through an authenticated capsule and
  assert that filesystem, generation, root snapshot, and replace capability
  appear together.
- Reject malformed BPB/geometry and prove canonical publication stays empty.
- Hold an operation while closing and require `Busy`; release it, close, and
  prove the publication disappears before capsule teardown is permitted.
- Copy an operation receipt, release one copy, and require the other copy to be
  stale.
- Fill the 64 operation slots and require bounded capacity failure without
  changing the active mount.
- Concurrently race two publishers from the same empty observation; exactly
  one commits. The unit spec covers the deterministic already-reserved case;
  transport-level concurrency evidence remains an integration acceptance item.
- Inject indeterminate lease release, require candidate-cleanup quarantine, and
  retry only the exact capsule seal. The current identity/capsule providers
  expose no failure-injection seam, so this remains an explicit integration
  acceptance item rather than a placeholder unit assertion.

No runtime evidence was collected in this implementation turn by instruction.
