# SimpleOS Memory Leveling Feature Requirements

Status: selected.

Selected scope: Feature Option A.

## Requirements

### REQ-001: Configurable Memory-Leveling Profiles

SimpleOS must expose a pure-Simple memory-leveling policy model with at least
three profiles:

- `baremetal_static`: fixed pools, no swap, no migration, DMA pin safety.
- `simpleos_default`: CPU DRAM plus optional swap and cold-page demotion.
- `heterogeneous_device`: CPU DRAM, swap, GPU-resident pages, NIC/RDMA
  registered pages, DMA-pinned pages, and shadow-copy decisions.

### REQ-002: Bare-Metal Simplicity

The `baremetal_static` profile must never select swap, migration, GPU, NIC, or
shadow-copy actions. It must still reject unsafe DMA/NIC/GPU page movement.

### REQ-003: Device-Pinned Safety

DMA-pinned, NIC-registered, and GPU-resident pages must fail closed for swap
or demotion unless the policy explicitly proves the action is safe.

### REQ-004: Default Swap/Demotion Policy

The `simpleos_default` profile must allow ordinary CPU cold pages to demote to
swap when swap is enabled and must keep hot pages in CPU DRAM.

### REQ-005: Heterogeneous Policy Shape

The `heterogeneous_device` profile must represent GPU, NIC/RDMA, DMA-pinned,
and shadowed states separately so later hardware integration can reuse the same
policy boundary without changing callers.

### REQ-006: Simple Language Model Boundary

The policy must align with the existing Simple memory/capability model: movable
ordinary pages are treated separately from pinned/registered/externally visible
device pages. This selected slice does not add new language syntax.

### REQ-007: No Hardware Completion Claim

This implementation must not claim real GPUDirect, RDMA hardware paging, CXL,
or live GPU/NIC migration. Model evidence is valid only when labeled as model
evidence.
