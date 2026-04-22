# FR-NET-0006 Local Research — RDMA Exoskeleton Transport

Status: implemented research note.

Existing state:

- `NetBackendCapabilities` already had `supports_rdma` and tiering treated RDMA as strongest.
- No RDMA memory-registration, queue-pair, completion, or benchmark model existed.
- Architecture notes say RDMA should be a separate provider, not forced into the existing `NetworkDevice` abstraction.

Implementation:

- `std.io.rdma` adds explicit RDMA configuration, memory-registration lifetime records, queue pairs, completion records, and benchmark output.
- `rdma_net_backend_capabilities` reports RDMA only when the config is explicitly enabled and has a nonzero protection domain.
- Disabled config keeps portable TCP as the default path.
