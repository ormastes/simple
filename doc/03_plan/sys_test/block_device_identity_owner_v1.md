# Block-device identity owner v1 test plan

This lane adds focused executable contract examples only; it does not claim a
QEMU or filesystem-launch acceptance result.

- Create a seal and validate the exact backend identity and region.
- Reject changed region identity and overlapping active regions.
- Replace an active binding and prove its old seal and copied lifecycle value
  are stale.
- Unmount once and prove copied lifecycle authority cannot unmount twice.
- Prove unmount invalidates the observational seal.

Runtime execution is intentionally deferred under the active no-verification
instruction.
