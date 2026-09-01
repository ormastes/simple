# ARM64/RV64 WM input ingress constructors

Status: constructor implemented; composition-root migration pending.

Implemented:

- ARM64 VirtIO-MMIO and RV64 VirtIO-PCI readiness-gated constructors.
- Architecture-local single-owner decoder storage.
- Opaque bounded-registry handle publication with zero as the fail-closed result.
- One-event delivery and bounded raw-pump implementation; idle allocation
  behavior has not been measured or runtime-verified.

Pending:

- Replace the direct decoder ownership in each production desktop entry with
  the registry handle without losing current device/IRQ/frame evidence.
- Do not enable both paths concurrently: they would consume the same hardware
  event queue through two decoder states.

Verification: not run by explicit user instruction.
