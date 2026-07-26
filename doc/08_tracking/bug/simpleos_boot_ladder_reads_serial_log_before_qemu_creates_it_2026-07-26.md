# SimpleOS boot ladder reads serial.log before QEMU creates it — mis-attributes render faults as boot failures

- **ID:** simpleos_boot_ladder_reads_serial_log_before_qemu_creates_it_2026-07-26
- **Date:** 2026-07-26
- **Area:** SimpleOS showcase/QEMU harness — the "UEFI boot ladder" evidence
  section of the production spec lane
- **Severity:** medium — no product defect; it corrupts *evidence*, sending
  investigations to the wrong subsystem.
- **Status:** OPEN

## What happens

On the 2026-07-26 linux-x86_64 SimpleOS-WM × QEMU run the ladder printed:

```
  [MISS] GRUB EFI app ran (OVMF -> bootloader OK)
  [MISS] multiboot handoff -> kernel _start (shared crt0.s)
  cannot open build/.../serial.log: No such file
```

while the same run's final `serial.log` was **181,501 bytes** and contains
`grub`, `multiboot loading`, and `_start` (x3), plus a working NVMe controller
and FAT32 mount. The ladder evaluated its markers before QEMU had created the
serial log file, reported every rung as MISS, and the honest failure — a guest
render fault (`content-provenance-rejected` → `window-degraded`) — read as a
boot failure.

## Impact

A reader triaging from the ladder alone would investigate OVMF/GRUB/multiboot,
all of which worked. The real fault that run was in the guest renderer
(`[web-layout] degenerate-parse html_len=5794 nodes=0 split_parts=18`).

## Fix direction

Evaluate ladder markers only after QEMU exit (or after the serial log exists
and is quiescent), and make "log file absent at check time" its own explicit
ladder state distinct from "marker absent in log".

## Related

- `doc/09_report/rv64_display_smoke_qmp_probe_2026-07-25.md` — same lane
- `doc/08_tracking/bug/simpleos_wm_content_provenance_material_fallback_none_2026-07-25.md`
  — the real fault the MISS lines obscured
