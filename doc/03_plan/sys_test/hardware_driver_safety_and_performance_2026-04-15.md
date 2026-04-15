<!-- codex-design -->
# Hardware Driver Safety And Performance System Test Plan

## Phase 1 checks

1. `virtio_blk` no longer uses fixed scratch addresses.
2. Read/write requests allocate explicit DMA request buffers.
3. Timeout and error paths free descriptors and DMA buffers.

## Phase 2 checks

1. `virtio_blk` supports selectable completion mode.
2. `virtio_net` supports selectable completion mode.
3. Polling remains available as a fallback.

## Phase 3 checks

1. zero-copy APIs preserve explicit ownership
2. caller-visible completion boundaries are clear

## Phase 4 checks

1. `SYS-GUI-008` reaches `render-ready`
2. virtio-gpu remains labeled experimental until that passes
3. direct QEMU boot and `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl` agree on the same healthy path
