# `rt_file_read_bytes` halts the kernel instead of degrading when no VFS is present

**Date:** 2026-07-17
**Status:** fixed / landed (`c9b5e0beabb`)
**Severity:** P1 — a font read on a baremetal build with no VFS mounted halted
the kernel instead of degrading gracefully.
**Component:** baremetal runtime stub —
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`.

## Symptom

When the font-read path called `rt_file_read_bytes` on a baremetal build where
no VFS/filesystem was available (early boot, or the NVMe/FAT32 mount not yet
ready), the stub halted the kernel rather than returning empty and letting the
font layer fall back to a bundled/placeholder path.

## Root cause

The baremetal `rt_file_read_bytes` stub treated a missing filesystem as a fatal
condition (halt) instead of a soft-degrade. The font read chain expects an empty
result to trigger its fallback, not a halt.

## Fix

`c9b5e0beabb` fix(os/runtime): `rt_file_read_bytes` returns empty instead of
halting on baremetal (no-VFS degrade). The stub now returns an empty buffer so
the caller degrades to its fallback path.

## Affected files

- `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`

## Related

- `os_wm_font_fallback_placeholder_degrade_2026-07-17.md` — the WM-side degrade
  policy that consumes this empty result.
- `desktop_kernel_ovmf_render_pagefault_vs_kernel_clean_2026-07-18.md` — the
  in-guest font read chain (NVMe 64-bit BAR high-half map) that, once working,
  supplies real bytes on this path.
