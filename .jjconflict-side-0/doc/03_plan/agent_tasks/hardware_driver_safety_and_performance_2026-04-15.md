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
- Keep `SYS-GUI-008` as the explicit check/fix lane for virtio-gpu

## Agent C: NVMe and future NIC/RDMA groundwork

- Harden NVMe queue and DMA invariants
- Document plain NIC integration plan
- Keep RDMA work isolated from `NetworkDevice`

## Main-thread integration

- Keep `SYS-GUI-008` on the active plan until the direct QEMU lane and the baseline spec are both green
- Do not merge acceleration claims ahead of that gate
