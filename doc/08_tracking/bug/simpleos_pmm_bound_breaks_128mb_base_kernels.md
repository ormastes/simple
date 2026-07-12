# BUG: committed pmm bound kernel_end=0x14000000 overlaps 128MB-base kernel RW — green stream baseline unbuildable from origin

**Status:** RESOLVED (2026-07-12)
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

## Resolution (2026-07-12)

All x86_64 entry files' pmm reserve bound raised 0x14000000 → 0x18000000
(384 MiB; constraint comment added at each site; TODO notes the linker-symbol
derivation upgrade path). 8 entries fixed: clang_stream, fs_elf_exec_smoke,
ring3_smoke, fs_exec_general, desktop_e2e, ssh_ring3, gui_entry_desktop
(reserved_end const), fs_exec_stream. fs_exec_prod entry has no such bound
on origin. Safety check: the only sub-384MB QEMU configs (-m 256M
abi/modinit probes) boot entries that do not use this bound; all affected
entries run at 512M+.

Verified: 124.6 MB clang_static streams to completion (PASS stream-open,
no FAT-state corruption; the downstream abort-134 is the separate
module_vs_entry/source regression); ssh_clang_hello_ring3 FULL green;
ssh_multi_cmd green; disassembly shows mov $0x18000000 in the built kernel.
