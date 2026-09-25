# Mounted FAT32 positioned read cannot stream big files: Fat32Core.read_cluster caches every cluster into the driver (unbounded)

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up), Wall 9 payload loader design
Severity: design constraint (not a crash): any file larger than ~heap/8 bytes
read through the mounted positioned path exhausts the freestanding heap even
when the caller never materializes the payload itself.

## Context

Wall 9 tasked the lane with reading the 115,209,168-byte /CLANG.ELF payload
into a raw region without materializing one tagged `[u8]` (8 B/RuntimeValue
~= 922 MB > the 512 MiB freestanding bump heap).  The obvious shape — chunked
`g_vfs_positioned_read_at` calls (<= 1 MiB each) with a per-chunk copy into
the raw region — is disqualified by THREE stacked tagged materializations in
the mounted read path, one of which no heap watermark can reclaim:

1. `driver_positioned_read_bytes` (src/lib/nogc_async_mut/fs_driver/
   mount_table_support.spl:68) calls `alloc_zeroed_bytes(length)` — a tagged
   `[u8]` of `length` elements (8 B each) allocated per call.
2. `_positioned_prefix` (mount_table_support.spl:51) copies the result into
   ANOTHER tagged array, element-by-element push.
3. **Fatal:** `Fat32Core.read_cluster` (src/lib/nogc_async_mut/fs_driver/
   fat32_core.spl:432) caches EVERY cluster it reads into the driver object
   fields `_cluster_cache_keys` / `_cluster_cache_values`
   (fat32_core.spl:138-139, unbounded put at :417-430, invoked at :457).
   The pread path reaches it via `me fn read` (fat32_file_ops.spl:491,515).
   For the 115 MiB payload that is ~3,513 clusters x 32 KiB x 8 B
   ~= 879 MB of tagged arrays held by the driver for the rest of the boot —
   the same 922 MB wall via the back door.  Because the cache arrays are
   driver-long-lived state, a mark/release heap watermark around each chunk
   would strand the driver's cache pointers into released memory (use-after-
   reuse on the next `_cluster_cache_lookup`).

## Consequence

The mounted positioned read is fine for metadata (open/fstat — Walls 6/8)
and small files, but it can never be the byte source for a payload whose
tagged size exceeds the heap.  The payload loader must pump bytes through a
stateless path (the direct cluster walker) into a raw region outside the
heap — see `arm_fs_exec_stream_payload_resident_v1`
(src/os/services/vfs/arm_fs_exec_vfs.spl) and the Wall 9 session section in
doc/08_tracking/aarch64_in_guest_clang_compile_lane_status_2026-09-25.md.

## Notes for the runtime/lib lane

- Any future bounded-cache design (e.g. an 8-entry LRU) would make the
  mounted path stream-safe; today the cache is unbounded by construction.
- The freestanding heap is a no-free bump allocator
  (baremetal_stubs.c `free` is a no-op), so "transient" per-chunk garbage is
  NEVER reclaimed unless a watermark is used — and watermarks are only safe
  around stateless callees.
