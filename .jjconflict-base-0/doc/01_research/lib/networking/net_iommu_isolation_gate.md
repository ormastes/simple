# FR-NET-0009 Local Research — IOMMU Isolation Gate

Status: implemented research note.

Existing state:

- `DeviceGrant` already carries `iommu_domain_id` and `iommu_cap`; zero values represent no IOMMU domain.
- Kernel DMA allocation tracking already records owner task, owner device, cache policy, size, and allocation id.
- `std.io.sriov.sriov_assign_vf` already fails closed when the SR-IOV physical function has no IOMMU domain.

Implementation:

- `device_grant_is_isolated` and `device_grant_is_no_isolation` make the grant isolation marker explicit.
- `dma_descriptor_matches_owner` validates task and BDF ownership before DMA reuse.
- `net_backend_sriov_isolation_state` reports `sriov-available` separately from `sriov-isolated`.

This keeps no-IOMMU systems usable for trusted early-boot drivers without advertising isolated SR-IOV/user-owned DMA acceleration.
