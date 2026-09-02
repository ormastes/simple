# Payload widening (D1-D3) reached only the behavioural backend, not the Vt-physics emulator

**Date:** 2026-09-01
**Found by:** the emulator-media spec agent; **verified by the parent.**
**Status:** OPEN. Scopes what "the payload is widened" may be claimed to mean.

## Measured

```
grep -c PageData fw/fil_nand_emu.spl     -> 0
grep -c PageData fw/fil_nand_device.spl  -> 11
```

`fw/fil_nand_emu.spl:197` `program(...)` still does `c.data_in(data & 0xFF)` at
column 0 only, and `read_page` streams column 0. **The Vt-physics emulator backend
has no `PageData` at all.** D1-D3's real 4096-byte pages live only in
`fw/fil_nand_device.spl:62` (`page_data: [PageData]`) — the *behavioural* backend.
The emu-backed `Fmc` holds the behavioural device but never routes page data to it
(`fw/fil_fmc.spl:61-62,90`).

Geometry also differs and does not match the firmware profile:
`src/lib/hardware/nand_emu/nand_types.spl:46` — emu `page_bytes` is **528**
(S1/S2) or **4224** (S3), including spare. `fw/nvme_payload.spl:31` declares
`PAGE_BYTES = 4096`. These are three different page sizes.

## Direct evidence from a live host write

Host write `0xA5` to lba0 through `nvme_controller_new_emu()`, then
`ftl.emu_vt_histogram(ppn)`:

```
ppn=0  bins=256  cells=4224
nonzero: [88]=4220 [148]=1 [150]=1 [152]=1 [154]=1
```

4224 cells exist; the host write programmed exactly **4** of them — the 4 set bits
of `0xA5`. 4220 cells remain erased.

## Why this matters

The D1-D3 report was accurate in its own terms ("`fil_nand_emu.spl` is untouched —
physics backend, own S1 geometry") but the consequence was not drawn out:
**the one path that has real NAND physics is the one path that still stores a
single byte.** So "the payload is widened" is true of the behavioural backend and
false of the emulator, and any test asserting full-page storage *through the
emulator* cannot pass today.

This also means a page-wide retention/wear/ECC scenario over Vt physics — the
whole point of the emulator — still exercises one byte per page.

## Required

1. Route `PageData` through `fil_nand_emu.spl` (program/read_page across all
   columns, not column 0), or state explicitly that the emu backend is
   byte-granular by design and stop implying otherwise in plan documents.
2. Reconcile the three page sizes (4096 firmware / 528 S1-S2 emu / 4224 S3 emu),
   or make the profile mismatch an explicit, checked configuration rather than a
   silent divergence.
3. Until then, do not write or accept a test claiming full-page storage through
   the emulator. The Vt histogram is the only honest page-wide evidence the emu
   currently exposes.

## Caveat

Measured on the Rust bootstrap seed. Same caveat as the sibling records; the
finding is structural (a symbol is absent from a file) and does not depend on
runtime behaviour.

## Resolved 2026-09-01 (items 1 and 2)

`fw/fil_nand_emu.spl` now carries `PageData`. The backend moved from NeProfile.S1
to **S3**, chosen by the checked identity `PAGE_BYTES + OOB_BYTES == page_bytes`
(4096 + 128 == 4224); S1/S2's 528-byte page physically cannot hold a firmware
page, which is why this backend stored a byte. `emu_geometry_ok` asserts the
identity at construction and `nand_emu_new` fails closed (zero backed
pages/blocks -> every op NAND_BAD_BLOCK) rather than narrowing silently.

* `program_page` drives all 4096 main columns through the ONFI `data_in`
  handshake (word i little-endian at columns 8i..8i+7); the 128 spare columns
  stay at the FFh preset and OOB stays in the side arrays, as fil_nand_device
  keeps it out of `page_data`. `read_page_data` streams them back.
* `fil_fmc.spl`'s narrowing shim is GONE: `dev_program_page` calls
  `e.program_page`, `dev_page_data` calls `e.read_page_data` (its dead
  `fallback` param was dropped).
* The scalar seam (`program` / `read_page.data` / `err`) is deliberately
  unchanged and still column-0 scoped — `err` feeds the scalar fil_ecc decoder
  and the landed reliability ladder, whose oracles are byte-scoped
  (rel_seams_check: "exactly ONE programmed cell in column 0"). Widening `err`
  page-wide was implemented, measured and reverted: it is real (an aged worn page
  shows extra drifted cells elsewhere, turning corrected 1 into 2) but it is
  ECC-widening work in fil_ecc.spl / fil.spl, not payload widening.

Witness: `fw/emu_payload_widening_witness_check.spl` ("EMU PAYLOAD WIDENING
WITNESS OK"), the emulator sibling of payload_widening_witness_check. Measured:

    byte path (Fmc.dev_program, column 0)  programmed =     4 of 33792 cells
    page path (program_page, all-zero pg)  programmed = 32768 of 33792 cells
    aged worn page (3000 P/E, +1 year)     512 of 512 words sense different
                                           from what was written

Non-vacuity verified by re-inserting the shim: the witness then FAILs on words
1/100/255/511 (all read -1) and on both cell counts (page path 8, not 32768).

Window change: S3 backs 16 blocks x 8 pages, not S1's 8 x 4, so the fold-collision
LBAs in `fil_nand_emu_e2e_check.spl` moved from 4 to 8; that check was ported to
the new window (same property, new geometry) and is green.

Perf: no regression. The emulator ALREADY looped every `page_bytes * 8` cell on
each program/read (unwritten columns preset to FFh), so the feared "~4000x more
simulated cells" never existed — only the data_in/data_out streaming loops are
new. Full fw check suite (42 files) runs in the same envelope as before; the
widened witness itself is 1.9s.

### Perf caveat found after the fact — rel_wiring_check now flirts with the 10s cap

The "no regression" line above is right about the SUITE but wrong about one file.
S3 raises per-op cell work 8x (33792 vs 4224 cells swept per program and per
sense), and `rel_wiring_check.spl` is the emu check with the most device ops:

    baseline (S1)   1.5s / 2.7s / 3.9s across three same-session runs
    widened (S3)    4.5s in the suite; 9.7 / 9.8 / 10.0s measured in isolation
                    under load avg 33, and ONE run aborted with
                    "error: example timed out after 10s"

Every other check is well clear (next worst: nvme_multiblock_witness 4.8s,
admin_transport 3.5s, nvme_emu_recovery 2.0s). This is load sensitivity on a
shared box, not a hang — the check passes and prints REL WIRING OK whenever it
is allowed to finish (`SIMPLE_TIMEOUT_SECONDS=0`). But it now sits on the
boundary and WILL flake on a busy machine.

The cost is inherent, not incidental: 4096-byte pages require S3, and the
emulator's per-cell physics loops live in `src/lib/hardware/nand_emu/chip.spl`
(`ne_chip_do_read` / `ne_chip_do_program`), outside the firmware. Mitigations, in
order of preference, none applied here:
  1. Shrink what rel_wiring_check exercises (fewest device ops for the property).
  2. A coarse mode in the NeChip: full per-cell fidelity on a sampled column
     subset, bulk-evolve the rest. Library change, needs its own gate.
  3. Raise the example timeout for this one check.
