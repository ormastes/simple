# BUG: committed pmm bound kernel_end=0x14000000 overlaps 128MB-base kernel RW — green stream baseline unbuildable from origin

**Status:** open (one-line fix known and verified for streaming; needs gate-verified landing)
**Severity:** medium-high (fresh builds of the clang streaming path corrupt FAT stream state; masks/compounds the seed regression)
**Component:** x86_64 fs-exec streaming loader pmm bounds (src/os/kernel/loader/x86_64_fs_exec_ring3.spl area)
**Found:** 2026-07-12 (bisection lane, green-repro attempt)

## Symptom

Rebuilding the "proven green" streaming smoke from origin/main fails during
streaming: the pmm bitmap/frames bound uses kernel_end=0x14000000, but a
128MB-load-base kernel's real RW end is ~0x17608000 — pmm hands out frames
inside live kernel .bss and streaming zeroes the FAT stream state (~21 MB in).
The entry file's own comment prescribes 0x18000000; the committed code
disagrees.

## Fix

Raise the bound to 0x18000000 (or better: derive from the linker-provided
kernel end symbol instead of a constant). Verified in bisection Builds F/G/H:
with 0x18000000 streaming completes correctly (the remaining abort 134 in
those builds is the separate seed regression, see
`x64_freestanding_module_vs_entry_ring3_handoff.md`).

Landing requires: SSH hello + multi-cmd gates green + one streaming run
showing full-file stream completion, with the fix as the only loader change.
