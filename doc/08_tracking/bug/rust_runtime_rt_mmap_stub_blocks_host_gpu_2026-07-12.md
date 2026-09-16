# Rust runtime rt_mmap stub blocks the host-GPU daemon

After a strict no-stub native build linked the current host-GPU daemon with
zero undefined `rt_*` symbols, its empty 8 MiB one-shot probe returned
`simpleos_gpu_host: mmap failed` (exit 3).

The selected runtime owner currently hardcodes `rt_mmap(...) -> 0` and treats
`rt_munmap`, `rt_madvise`, and `rt_msync` as unconditional success in
`runtime/src/value/sffi/file_io/file_ops.rs`. These placeholders must not be
accepted as host-GPU evidence.

Implement real Unix file-backed shared mmap/munmap/msync/madvise at the runtime
owner, with Windows equivalents or explicit unsupported results. Verify with a
file-backed cross-process visibility test before rerunning QEMU receipts.

## Resolution (2026-07-13)

The Rust runtime owner now implements Unix `MAP_SHARED` file mappings with
bounded offset/length validation, real `msync`, `madvise`, and `munmap` calls,
and explicit unsupported results on non-Unix targets. The file descriptor is
closed after `mmap`; the mapping retains its independent kernel lifetime.

Evidence:

- `test_shared_mmap_cross_process_visibility`: PASS. A child-process write is
  visible through the parent mapping, and a parent write plus `MS_SYNC` is
  visible to a second child. Invalid ranges/advice fail closed and readonly
  remapping observes the persisted sentinel.
- Fresh full bootstrap: Stage 2 and Stage 3 PASS.
- Strict current host-GPU daemon: zero generated stubs and zero undefined
  `rt_*` symbols; the shared file maps and a captured ARM HELLO is processed.

The subsequent HELLO rejection is not an mmap failure. A Vulkan-feature runtime
returns success from `rt_vulkan_init`, while the current Engine2D Vulkan backend
still fails later in initialization; that separate backend blocker remains
tracked rather than being masked with a synthetic receipt.
