# SimpleOS NVFS Submodule Migration — Feature Requirements

## Selected Requirement Set
- REQ-NVFS-MIG-001: NVFS source must live under the repo-owned SimpleOS tree, not as `examples/11_advanced/nvfs`.
- REQ-NVFS-MIG-002: Migrated NVFS imports must use `os.services.nvfs.*`.
- REQ-NVFS-MIG-003: `.gitmodules` must not register `simple-nvfs`.
- REQ-NVFS-MIG-004: The old `examples/11_advanced/nvfs` working tree and gitlink must be removed.
- REQ-NVFS-MIG-005: Active SimpleOS/storage docs must point to the new OS-owned NVFS path.
- REQ-NVFS-MIG-006: The external `ormastes/simple-nvfs` GitHub project must be deleted after local migration evidence is collected.
