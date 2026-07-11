# In-guest clang — roadmap and current blocker

**Goal:** run clang natively ON SimpleOS (guest compiles hello.c itself), vs the
current host-clang-builds-the-ELF flow.

## The shape of the work

Running clang in-guest = the ring-3 FS-exec loader at scale. clang-20 is
**131,052,368 bytes (125 MiB)**, so two ceilings must fall:

1. **4 MiB whole-file read cap.** `examples/09_embedded/simple_os/arch/x86_64/
   boot/baremetal_stubs.c:2742` — `static uint8_t
   simpleos_fat32_path_read_buf[4194304]`; files larger are rejected (~line
   2870). clang is 31× over. A 125 MB file also can't be a single physically
   contiguous buffer.
2. **Correct fix (already have the primitive):** `simpleos_fat32_stream_read_at(
   file_off, dst, len)` (baremetal_stubs.c:2712) is a true random-access FAT
   streamer (walks the cluster chain via a one-cluster scratch, arbitrary
   offset) that does NOT use the 4 MiB buffer. The loader should stream each
   `PT_LOAD` segment directly into `pmm_alloc_page_raw` frames in
   `src/os/kernel/loader/x86_64_fs_exec_ring3.spl::_map_pt_loads`, replacing the
   whole-file buffering. This removes the cap and scales to 125 MB.

Secondary (necessary but after the above): clang's static-link GOT/SIGSEGV fix
(see clang_static/GOT bug docs), and ≥512 MB guest RAM.

## Blocker that stops everything first (2026-07-11)

Before scale matters, the **4,728-byte** `/FSEXEC.ELF` fails to materialize in
the `fs_exec_prod_ring3_entry` / `fs_exec_general_ring3_entry` lanes on a
from-source rebuild at origin tip:

```
[prod] /FSEXEC.ELF read size=4728 buf=0x0D5D8020   <- stream_open+read report success (n>0)
[prod] blob materialized len=4728 magic=248,3,0,0  <- [u8] readback bug (0x7F<<3), loader ignores it
[spawn] FAIL blob not ELF ... w0=0                  <- mmio readback of the buffer is ZERO
```

`stream_read_at` returns n>0 (no failure branch) but the destination buffer
reads back zero via mmio. The buffer `0x0D5D8020` (~224 MB) is inside vmm_init's
0..4 GB identity map (PRP=virt=phys valid), so this looks like an **NVMe
read-data DMA completion/coherence failure post-vmm** — the CQ reports success
without the data landing. Same family as
`doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md`;
`vmm_map_nvme_bar_high()` fixed the doorbell MMIO but not the read-data DMA.

NOTE: the SSH demo (`ssh_ring3_entry`) uses a BOOT PRELOAD (reads /FSEXEC.ELF
BEFORE vmm_init into the static buffer, then short-circuits) and is guarded by
`mmio_disable_test_mode()`, so it is not necessarily subject to this post-vmm
read failure — but the `prod`/`general` entries' post-vmm read path must be
fixed before the streaming-loader work, and the SSH demo's current-tip status
should be re-confirmed.

## Order of work

1. Fix the post-vmm NVMe read-data DMA (the buffer must actually receive the
   bytes the CQ says it did) — in the `nvme_*` / `_fat32_read_cluster`
   DMA-completion path in baremetal_stubs.c.
2. Replace whole-file 4 MiB buffering with per-`PT_LOAD` `stream_read_at` into
   `pmm` frames in `x86_64_fs_exec_ring3.spl::_map_pt_loads`.
3. clang static-link GOT fix + ≥512 MB RAM; then attempt clang in-guest.
