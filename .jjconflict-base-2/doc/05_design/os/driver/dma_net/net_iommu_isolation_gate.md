# FR-NET-0009 Design — IOMMU Isolation Gate

Device grants:

- `iommu_domain_id != 0` and `iommu_cap != 0` means isolated.
- Zero `iommu_domain_id` or zero `iommu_cap` is the explicit no-isolation marker.

DMA:

- `DmaDescriptor` already carries owner task and owner BDF.
- `dma_descriptor_matches_owner` provides a reusable validation point before cross-driver reuse.

SR-IOV:

- `sriov_assign_vf` requires the physical function to carry a nonzero IOMMU domain.
- `sriov_net_backend_capabilities` only sets `supports_sriov` for assigned and isolated VFs.
- `net_backend_sriov_isolation_state` reports available-but-unisolated SR-IOV separately from isolated SR-IOV.
