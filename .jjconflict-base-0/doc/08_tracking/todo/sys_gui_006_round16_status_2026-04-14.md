# SYS-GUI-006 — Round 16 Status (2026-04-14)

## TL;DR

- **NOT LIVE-GREEN.** Desktop boots, paints, and emits `[desktop-e2e]
  desktop-ready` + `[desktop-e2e] paint-settle:done`. QMP socket opens.
  But QEMU hits `[PANIC] heap exhausted` in the post-marker
  `launcher_shortcut_dispatch` path before the spec's QMP screendump
  command can be serviced. No PPM captured. Result: `2 passed, 1 failed`
  (build + baseline-dir pass; live capture fails).
- **New in Round 16 vs Round 14:** Both previously-documented host
  environment blockers (missing `bin/simple` symlink, missing `socat`)
  were resolved. The build now passes (kernel ELF 5.1 MB). The QMP
  socket is created. Socat shim (`python3`-backed) works. The OS-side
  heap panic is the sole remaining blocker.
- **Root cause is OS-side, not harness.** QEMU crashes ~250 ms after
  the paint markers, identical to Round 12 measurement. The
  `launcher_shortcut_dispatch(KEY_B, META_MODIFIER)` → NVMe missing →
  `manifest read failed` → heap exhausted sequence needs an OS fix.

## Run Evidence

### Attempt 1 — stale cache replay
Old `test-result-cache-rs.txt` entry replayed Round-13 result
(`1 passed, 2 failed, 2504 ms`). Cache cleared manually.

### Attempt 2 — first live QEMU run (without socat)
```
builds desktop_e2e_entry.spl into a baremetal kernel  ✓  (27s)
[simpleos_desktop_fb_spec] R13 pre-wait sleep for serial-log flush
[qmp] screendump failed: /bin/sh: 1: socat: not found
[simpleos_desktop_fb_spec] QMP screendump failed
[simpleos_desktop_fb_spec] captured 0x0, non-black pixels: 0 of 0
✗ boots desktop, captures framebuffer via QMP, and matches baseline
  semantic: method `len` not found on type `enum` (receiver value: Option::Some([]))
✓ has a baseline directory for simpleos_desktop_framebuffer captures
3 examples, 1 failure  FAILED (29071ms)
```
Serial log confirmed: `[desktop-e2e] desktop-ready` and
`[desktop-e2e] paint-settle:done` reached. Socat missing from host.

### Attempt 3 — with python3 socat shim in PATH
Added `/tmp/simple-round23/bin/socat` (python3 unix-socket bridge).
PATH set to include workspace bin/ at test runner invocation.
```
builds desktop_e2e_entry.spl into a baremetal kernel  ✓
[simpleos_desktop_fb_spec] R13 pre-wait sleep for serial-log flush
✗ boots desktop, captures framebuffer via QMP, and matches baseline
  semantic: method `len` not found on type `enum` (receiver value: Option::None)
✓ has a baseline directory for simpleos_desktop_framebuffer captures
3 examples, 1 failure  FAILED (30852ms)
```
Error changed from `Option::Some([])` to `Option::None` — confirming
socat now runs but QMP returns no data (QEMU exited before screendump).

Serial log tail for attempt 3:
```
[desktop-e2e] desktop-ready
[desktop-e2e] paint-settle:done
FAULT @ 0x0000000000459b4d
FAULT @ 0x0000000000459b71
FAULT @ 0x0000000000459b77
[nvme-c] No NVMe device found on PCI bus
[fat32-c] Failed to read sector 0
[launcher] manifest read failed path=/sys/apps/browser_demo file=BROWSER.APP
[launcher] Failed to launch Browser Demo: -2
[launcher] shortcut fallback key=66 mod=1
[PANIC] heap exhausted
```

## What Changed This Round (harness-level)

1. Added `bin/simple` symlink in `/tmp/simple-round23/bin/` pointing to
   the bootstrap binary. Previously missing from isolated jj workspace.
2. Added `python3`-backed `socat` shim in `/tmp/simple-round23/bin/socat`
   that proxies stdin→unix-socket→stdout for the `UNIX-CONNECT:` pattern
   used by `qmp_client.spl`. Run with `PATH=bin/:$PATH`.

Neither change is committed (workspace-only, no production code altered).

## Spec Results Summary

| Example | Attempt 2 | Attempt 3 |
|---|---|---|
| builds desktop_e2e_entry.spl | ✓ PASS | ✓ PASS |
| boots desktop, captures framebuffer | ✗ FAIL (no socat) | ✗ FAIL (QEMU exits) |
| has a baseline directory | ✓ PASS | ✓ PASS |
| **Total** | 2 passed, 1 failed | 2 passed, 1 failed |

## Root Cause (unchanged from Round 12)

QEMU exits ~250 ms after `[desktop-e2e] desktop-ready` because:

1. `desktop_e2e_entry.spl` calls `launcher_shortcut_dispatch(KEY_B, META_MODIFIER)`
2. NVMe is absent in the QEMU q35 config → manifest read fails for
   `browser_demo`
3. Heap is exhausted in the error path → `[PANIC] heap exhausted`
4. QEMU `isa-debug-exit` fires → QMP socket closes before screendump

The spec's pre-wait sleep (R13: ~250 ms) fires AFTER the paint markers but
the screendump request arrives after QEMU has already exited.

## Required OS-Side Fix

One of:

**Option A (preferred):** Increase QEMU heap for the e2e test image so
`launcher_shortcut_dispatch` can complete without OOM. Either enlarge
the static heap allocation in the linker script, or reduce allocations
in the shortcut/manifest read path.

**Option B:** Guard `desktop_e2e_entry.spl` against NVMe-absent case
so shortcut dispatch is skipped and QEMU stays alive long enough for the
QMP screendump (add `if nvme_available()` check before shortcut call).

**Option C:** In `qmp_client.spl`, send the screendump immediately after
QMP capabilities handshake (before the pre-wait sleep), since
`paint-settle:done` already confirms paint is done.

All three are out of scope for this agent round (guardrail: no edits to
`src/lib/` or `examples/`).

## Status: NOT LIVE-GREEN

sys-gui-008 remains blocked pending OS-side heap or shortcut-guard fix.

## Next Steps

- OS engineer: implement Option A or B above in
  `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` and/or
  linker script heap size.
- Alternatively, implement Option C in
  `src/lib/nogc_sync_mut/qemu/qmp_client.spl` (call screendump
  immediately after capabilities, before the pre-wait sleep).
- Re-run as Round 17 after fix lands.
- `socat` should be installed on the CI host (`apt-get install socat`)
  or the `qmp_send` command string should be updated to use `nc -U`
  which is already installed.
