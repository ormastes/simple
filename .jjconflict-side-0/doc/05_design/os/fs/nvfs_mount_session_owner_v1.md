# NVFS Shared-Interface Mount Session Owner V1

## Scope

This prerequisite closes the in-process lifetime gap between an NVFS mount and
copyable callers. It does not replace `MountTable`, open file descriptions, or
the NVFS driver. Connector integration remains a separate change.

## Contract

One module-private mutex-backed process registry is the sole mutable authority;
there is no copyable owner value. It admits at most 64 live sessions. Each
returned handle binds a slot generation, monotonic mount
identity, monotonic mount generation, and the complete block-interface
identity. Admission consumes `NvmeSharedFilesystemInterface` and reruns its
canonical lease policy, including provider, namespace window, queue identity,
rights/depth, shared-interface, and isolation requirements. It also reconstructs
the canonical three-consumer projection and rejects forged readiness fields.

Close invalidates all copies by advancing the slot generation. A terminal
generation retires its slot permanently; counters never wrap. Validation is
O(1), while admission scans at most 64 slots. Storage is bounded.

The registry is serialized through the common mutex guard, and copying a handle
cannot fork state. The handle is a capability-style identity only: it never
conveys namespace, queue, or driver ownership and cannot reconstruct a closed
session. Closed slots retain the prior lease only as bounded tombstone storage;
validation rejects them before consulting that payload.

## Integration boundary

The next connector change should construct the shared-interface record from an
already validated NVMe filesystem lease, open one session after driver mount,
validate it before every connector operation, and close it before driver
unmount. FAT32 and DBFS continue to consume the same underlying lease contract;
this owner does not create a private NVFS hardware path.

No runtime verification was performed for this artifact by instruction.
