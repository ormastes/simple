# FR-NET-0009 System Test Plan — IOMMU Isolation Gate

System spec: `test/system/net_iommu_isolation_gate_spec.spl`

Coverage:

- Device grants distinguish isolated domains from explicit no-isolation markers.
- DMA descriptors validate owner task and owner BDF before reuse.
- SR-IOV VF assignment fails without an IOMMU domain.
- Network capability reporting distinguishes `sriov-available` from `sriov-isolated`.
