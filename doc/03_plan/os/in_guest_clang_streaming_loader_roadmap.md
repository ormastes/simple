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

Secondary (necessary but after the above): ≥512 MB guest RAM. The clang
static-link GOT fix is DONE (0b073602d83: .got placed in simpleos.ld; in-guest
`-emit-obj` verified no-SIGSEGV).

## Blocker status (2026-07-11, updated): DMA hypothesis DISPROVEN

Instrumented verification on the prod entry disproved the earlier "post-vmm
NVMe read-data DMA failure" theory entirely:

- Device side is correct post-vmm: `[rd-dbg] lba=49 dma=0x1981000 b=127,69,76,70`.
- C memcpy writes AND reads back the ELF correctly even at the previously
  "bad" destination (`[wr-probe] dst=0x0d5d4120 done=4728 out=127,69,76,70`).
- At origin tip (≥55c8bdf963b) the full post-vmm path passes from source:
  stream_open/read → ELF magic 127,69,76,70 → ring-3 exec → FSEXEC_OK rc=42.

The residual defect is a **compiler bug, not an OS/DMA bug**: freestanding
`rt_mmio_read_u8` returns 0 at addresses (~0x0D5Dxxxx region) where a plain C
load reads the correct byte — address/layout-dependent, latent at tip, only
manifests when .bss layout shifts the buffer into the bad region. Tracked in
`doc/08_tracking/bug/x64_freestanding_mmio_read_u8_address_dependent_zero.md`.
`doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md` was an earlier
sighting of the same family.

## Order of work

1. Streaming loader: replace whole-file 4 MiB buffering with per-`PT_LOAD`
   `stream_read_at` into `pmm` frames in
   `x86_64_fs_exec_ring3.spl::_map_pt_loads` (post-vmm reads are proven good).
   Parse via the raw-buffer mmio path, NOT the boxed `[u8]` channel (still
   boxing-broken: magic reads 248,3,0,0 = 0x7F<<3).
2. Rebuild with current `arch_x86_64_early_init`, which disables MMIO test mode
   before reads; retained C streaming already returned valid ELF bytes.
3. ≥512 MB RAM; put clang-20 on the FAT image and run the current
   `-emit-obj /hello.o` lane. Require the fail-closed ELF REL/main/exit-0 gate;
   historical bitcode and host-produced objects do not count.
