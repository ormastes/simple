# FR-NET-0005 Local Research — SR-IOV Discovery and Assignment

Status: implemented research note.

Existing state:

- `NetBackendCapabilities` already had `supports_sriov`, but there was no model for discovery, assignment, or isolation gating.
- `DeviceGrant` already carries `iommu_domain_id`; zero means no IOMMU domain.
- The repo did not have a pure PCI SR-IOV capability scanner suitable for default CI.

Implementation:

- `std.io.sriov` adds SR-IOV capability records, discovered physical functions, and VF assignment results.
- `sriov_scan_physical_functions` filters PCI capability records for SR-IOV capability id `0x10` with nonzero VF count.
- `sriov_assign_vf` fails closed without explicit opt-in, out-of-range VF index, or nonzero IOMMU domain.
- `sriov_net_backend_capabilities` reports `supports_sriov` only when assignment is both assigned and isolated.

QEMU/no-hardware fallback: default capability records are empty, so no physical functions are found and portable socket behavior remains the default.
