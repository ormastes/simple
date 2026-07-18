# BUG: freestanding rt_mmio_read_u8 returns 0 at addresses a C load reads correctly (address/layout-dependent)

**Status:** open (latent at origin tip; reproduces only when .bss layout shifts the FAT buffer to ~0x0D5Dxxxx)
**Severity:** high (silently corrupts any pure-Simple raw-buffer readback; masqueraded as an "NVMe DMA failure" and misdirected a whole roadmap)
**Component:** freestanding native-build codegen — u64-address read path (MIR variable stability / mir_opt interaction)
**Found:** 2026-07-11 (in-guest clang Stage-1 lane; instrumented disproof of the DMA hypothesis)

## Symptom

In `fs_exec_prod_ring3_entry` lanes, with the static FAT read buffer at `0x0D5D4120`/`0x0D5D8020`:

- C side, same address, same run: `[wr-probe] dst=0x0d5d4120 done=4728 out=127,69,76,70` — memcpy wrote and read back the ELF correctly.
- NVMe DMA verified good post-vmm: `[rd-dbg] lba=49 dma=0x1981000 b=127,69,76,70`.
- Pure-Simple readback of the SAME address: `mmio_read8(blob+0)` → `rt_mmio_read_u8(0x0D5D4120)` → **0**; loader prints `[spawn] FAIL blob not ELF w0=0`.

So a plain C load reads 127 where the Simple-compiled read returns 0. A C memory barrier after the memcpy does NOT change it (rules out store-elimination on the C side).

## Trigger conditions

- Does NOT reproduce at origin tip `55c8bdf963b` (buffer lands at ~0x0D56Bxxx → reads correct, FSEXEC_OK rc=42 from source).
- Reproduces in a checkout with in-flight compiler mods (incl. `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`, mir lowering, backend) that shift `.bss` so the buffer lands in the `0x0D5Dxxxx` region — i.e. the bug is address/layout-dependent, not caused by those mods per se.

## Disproven hypotheses (do not re-chase)

- NVMe read-data DMA completion/coherence failure — disproven by `[rd-dbg]` device-side bytes.
- PRP virt/phys alias drift post-vmm — the C read at the destination address is correct.
- C-side store elimination — barrier tested, no effect.

## Suggested fix/regression

Regression: read back a raw buffer at a `0x0D5Dxxxx`-class address via `rt_mmio_read_u8` and compare with a C load of the same address. Domain owner: the freestanding MIR/codegen u64-address layer (same domain as `55c8bdf963b` "resolve MIR variables by stable names" and the var_reassign_ssa lane).

## Related

- `doc/03_plan/os/in_guest_clang_streaming_loader_roadmap.md` — blocker section corrected (was misattributed to DMA).
- `doc/08_tracking/bug/x64_ssh_kernel_fat32_stream_open_zero.md` — earlier sighting of the same family.
