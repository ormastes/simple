# Persistent SOSIX FS registry lifecycle v1

This focused model specifies the persistent kernel/service registry owner used
by positioned filesystem syscalls 134 and 135. The owner is a bounded value
that the runtime publishes after each accepted transition; it stores opaque
file and buffer identities, never userspace pointers.

## Register, refresh, lookup, retire

1. Authenticate the caller, service endpoint, and current service generation.
2. Register a capability in a free slot with a nonzero slot/generation, opaque
   file object ID, and explicit read/write rights.
3. Refresh only the same caller-owned slot and generation.
4. Resolve exactly one active caller-owned entry with the required right.
5. Retire by clearing authority and advancing the slot generation.

## Failure guarantees

- A different caller cannot refresh, retire, or resolve another caller's entry.
- A stale service or slot generation is rejected without mutating the owner.
- Capacity is bounded by `SOSIX_FS_SERVICE_MAX_CAPABILITIES_V1`.
- Reuse requires the post-retirement generation; stale handles stay dead.
- Positioned I/O continues through `read_at`/`write_at`; this lifecycle neither
  accepts raw addresses nor provides cursor save/seek/restore.

Executable specification:
`test/01_unit/os/sosix/fs_registry_lifecycle_v1_spec.spl`.
