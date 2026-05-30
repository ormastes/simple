# kernel-zstd-adapter — State

## Status: CLOSED — 2026-05-20

## Goal
Implement a minimal, noalloc-friendly Zstd decompressor for SimpleOS kernel
boot and initramfs decompression. No heap allocation — all state lives in
module-level `var` globals and caller-supplied `u64` pointer/length pairs.

## Status: DONE

## Phases
- [x] dev — zstd_noalloc.spl implementation (Raw + RLE block support)
- [x] research — RFC 8878 frame layout, noalloc constraints, extern availability
- [x] impl — committed to main
- [x] spec — zstd_noalloc_spec.spl (source-grep spec, baremetal extern-safe)
- [x] ship — all deliverables present and committed

## Deliverables
- `src/os/kernel/boot/zstd_noalloc.spl` — streaming Zstd decompressor
- `src/os/kernel/boot/zstd_noalloc_spec.spl` — spipe spec (source-grep, baremetal-safe)

## Design Decisions
1. **No arrays/Option/Result/text** — follows riscv_noalloc_* convention.
   Input/output via raw `u64` address + length pairs.
2. **Block types supported**: Raw (00), RLE (01). Compressed (10) blocks
   are detected and flagged as unsupported at boot stage — caller must
   use a pre-decompressed image or a future Compressed-block extension.
3. **State machine**: `ZstdState` enum encoded as u64 global — Init,
   ReadingFrameHeader, ReadingBlock, Done, Error.
4. **Fixed output buffer**: caller passes `out_ptr: u64, out_cap: u64`;
   module tracks `g_zstd_out_pos` write cursor.
5. **Checksum**: frame content checksum is skipped (not verified) at
   boot stage — integrity is guaranteed by the bootloader image signature.

## Zstd Frame Layout (RFC 8878)
```
Magic (4B: FD 2F B5 28)
Frame_Header:
  FHD (1B): FCS_Flag[7:6], Single_Segment[5], Content_Checksum[2], DID[1:0]
  [Window_Descriptor (1B if not Single_Segment)]
  [Dictionary_ID (0/1/2/4B per DID)]
  [Frame_Content_Size (1/2/4/8B per FCS_Flag + Single_Segment)]
Blocks (repeated):
  Block_Header (3B): Last_Block[0], Block_Type[2:1], Block_Size[23:3]
  Block_Content (Block_Size bytes)
[Content_Checksum (4B if Content_Checksum flag set)]
```

## File Placement
`src/os/kernel/boot/` — alongside `riscv_noalloc_heap.spl`,
`riscv_noalloc_pmm.spl`, `riscv_noalloc_handoff.spl`.

## Completed
- [x] state.md created
- [x] zstd_noalloc.spl implemented (Raw + RLE block support, magic/header parse)
- [x] Committed with jj
- [x] zstd_noalloc_spec.spl created (source-grep spec; baremetal externs not callable in host interpreter — spec verifies API surface, constants, and structural constraints via rg)

## Note on spec approach
`rt_riscv_uart_put`, `rt_mem_read_u8`, `rt_mem_write_u8` are RISC-V baremetal
externs with no host runtime implementation. Direct invocation in interpreter
mode panics. The spec uses `rt_process_run + rg` (same pattern as
`baremetal_noalloc_constraints_spec.spl`) to verify API surface and structural
rules without triggering those externs.
