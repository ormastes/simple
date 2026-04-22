# FR-NET-0005 Design — SR-IOV Discovery and Assignment

Discovery:

- Hardware enumeration provides `SriovCapabilityRecord` values.
- `sriov_scan_physical_functions` returns only records with SR-IOV capability id `0x10` and at least one VF.

Assignment:

- `sriov_assign_vf` requires explicit opt-in.
- The requested VF index must be in range.
- `iommu_domain_id` must be nonzero; otherwise assignment fails closed.

Backend reporting:

- `sriov_net_backend_capabilities` enables `supports_sriov` only when the assignment is both assigned and isolated.
- Portable and no-hardware environments use empty records and therefore never advertise SR-IOV.
