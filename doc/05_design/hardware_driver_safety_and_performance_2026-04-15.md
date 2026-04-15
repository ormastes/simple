<!-- codex-design -->
# Hardware Driver Safety And Performance Detail Design

## Phase 1

Target:
Replace unsafe fixed-address request scratch space in `virtio_blk` with explicit DMA allocations owned by the request path.

Design:
- Allocate one contiguous DMA region per request:
  - header: 16 bytes
  - data: `count * sector_size` for reads or `sector_size` for writes
  - status: 1 byte
- Publish the physical addresses to the virtqueue descriptors.
- Use the virtual addresses for CPU-side header/data/status access.
- Free the DMA region after completion or any early error path.
- Add a read-side destination-buffer size check.

Expected outcome:
- removes hardcoded address aliasing
- aligns block-driver DMA contract with the rest of the device model
- keeps the current polling completion model intact while the safety issue is fixed first

## Phase 2

Target:
Add completion-mode selection (`poll`, `interrupt`, `auto`) to `virtio_blk` and `virtio_net`.

## Phase 3

Target:
Introduce zero-copy APIs using caller-owned DMA buffers.

## Phase 4

Target:
Finish `virtio_gpu` controlq DMA correctness using the same explicit ownership model.
