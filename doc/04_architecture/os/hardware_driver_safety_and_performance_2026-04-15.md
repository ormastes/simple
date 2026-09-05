<!-- codex-design -->
# Hardware Driver Safety And Performance Architecture

## Scope

This work hardens the existing hardware-driver substrate instead of expanding hardware breadth first.

## Architectural direction

1. Keep the current PCI/device-grant/DMA split.
2. Normalize all DMA-using drivers around explicit `(virt, phys)` ownership rather than fixed addresses or inferred physical mappings.
3. Add completion-mode selection at the driver boundary:
   - `poll`
   - `interrupt`
   - `auto`
4. Introduce zero-copy incrementally through caller-owned DMA buffers, not through implicit aliasing of ordinary heap memory.
5. Treat RDMA as a separate transport/provider layer with its own registration and completion model.

## Sequence

1. `virtio_blk` DMA safety and request-buffer ownership
2. shared VirtIO completion-mode API
3. zero-copy hooks in `virtio_blk` and `virtio_net`
4. `virtio_gpu` controlq correctness
5. NVMe queue invariant hardening
6. plain NIC groundwork
7. RDMA groundwork and implementation

## Risks

- Mixing GPU debug work with general VirtIO refactoring will slow both.
- Adding zero-copy before explicit ownership tracking would make corruption harder to debug.
- RDMA should not be forced into the existing `NetworkDevice` abstraction.
