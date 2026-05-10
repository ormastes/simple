# FR-NET-0005 System Test Plan — SR-IOV Discovery and Assignment

System spec: `test/system/net_sriov_assignment_spec.spl`

Coverage:

- PCI capability scan identifies SR-IOV physical functions from capability id `0x10`.
- VF assignment fails closed without explicit opt-in.
- VF assignment fails closed without IOMMU isolation.
- Network backend reports `supports_sriov` only for an assigned and isolated VF.
- Default no-hardware behavior is represented by empty capability records.
