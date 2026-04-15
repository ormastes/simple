<!-- codex-design -->
# Hardware Driver Safety And Performance Agent Tasks

## Agent A: VirtIO block/network hardening

- Land explicit DMA ownership in `virtio_blk`
- Add completion-mode selection scaffolding
- Prepare zero-copy call shapes for block/network

## Agent B: VirtIO GPU stabilization

- Isolate controlq DMA contract
- Prove desc/avail/used writeback correctness
- Reach `render-ready` before any acceleration claim changes

## Agent C: NVMe and future NIC/RDMA groundwork

- Harden NVMe queue and DMA invariants
- Document plain NIC integration plan
- Keep RDMA work isolated from `NetworkDevice`
