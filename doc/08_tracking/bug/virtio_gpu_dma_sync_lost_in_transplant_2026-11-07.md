# virtio-gpu managed-DMA CPU/device sync lost in tree transplant

- **Date:** 2026-11-07
- **Severity:** P1 for boards without coherent DMA; there is no QEMU symptom
- **Status:** fix-implemented

## Cause

The tree transplant `88aac2ffe28`, with the commit message "rebase(main): transplant current main tree onto release/1.0", replaced the virtio-gpu driver with an older snapshot. The same transplant landed on main as `bb3f6ab8ab2`. The commit message gives no reason for the removal, and the evidence below shows it was unintended:

- The kernel still implements syscalls 84 (AllocDma), 86 (DmaSyncForDevice) and 87 (DmaSyncForCpu).
- The driver kept the `*_allocation_id` fields and the setters for them, but always set the ids to 0 and never issued a sync.
- One caller, `framebuffer_sync_for_cpu()`, survived, and it called a method that had been deleted.

## Fix

- **Allocation:**
  - Allocation ids and `owner_device` are restored.
  - `alloc_dma` calls syscall 84 again when kernel DMA is available.
  - Kernel DMA is opt-in by the caller. `display_service` turns it on; the standalone `virtio_gpu_entry` keeps the wrapper allocator.
- **Sync:**
  - `_sync_allocation_for_device` and `_sync_allocation_for_cpu` are restored. An allocation id of 0 means the sync is a no-op that succeeds.
  - Command and response buffers are synced around `_send_command`. Framebuffer syncs are added around `flush` and `flush_rect`.
- **Failure paths:** after a timeout or a failed transfer, the buffers are handed back to the CPU on a best-effort basis, so later syncs do not wedge.
- **Known gap:** the control ring is not synced. The kernel maps DMA uncached, and the code says so in a comment.

## Evidence

- `test/01_unit/os/drivers/virtio/virtio_gpu_dma_sync_spec.spl` failed every test at first (0/7). It now passes 14/14.
- Existing virtio specs:
  - The 8 that passed before still pass.
  - `memory_leveling_contract` went from failing (0/2) to passing (2/2).
  - `virtio_gpu_recovery_spec` fails 0/11 both before and after, because the same transplant also deleted its recovery code. That code is not restored here.
- Not verified on QEMU or a board. Behavioural ordering is checked only by source order, because `syscall()` is a direct extern with no shim a test could replace.
