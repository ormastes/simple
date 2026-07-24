# SimpleOS WM Fullscreen

Status: **BLOCKED — no live x86_64 QEMU PASS was produced by this source-only
repair.**

Executable:
`test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`

The executable scenario runs
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` exactly once through
the standard process facade. It does not paint a host fixture or accept serial
markers as pixels.

## Primary flow

1. Boot the canonical pure-Simple x86_64 `gui_entry_desktop.spl` through the
   production QEMU wrapper.
2. Load the wrapper's retained `evidence.env` and report.
3. Require `/SYS/FONTS/NOTOSANS`, exactly 1,708,408 bytes, with SHA-256
   `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
4. Require the independent QMP `pmemsave` right-56-by-bottom-48 RGB crop:
   8,064 bytes with SHA-256
   `addf76edf6d23ca9bea6d698ca1d30bc4bd8dd684bb50ff3158ef755bd2854fc`.
5. Require the same crop oracle to reject the retained one-byte-corrupted copy.
6. Require valid baseline, maximized, and restored PPM captures.
7. Require nonzero detected scanout metadata, exact capture size, distinct
   baseline/maximized hashes, and monotonic maximize/restore/pointer sequences.
8. Require keyboard, restore, pointer press, and pointer release IRQ, WM-state,
   and later frame markers to carry those exact sequences.

## Outcomes

- Wrapper exit `0`: the scenario checks the retained crop, corrupted copy,
  three PPM files, device origin, font identity, and correlated input markers
  before accepting the bundle.
- Wrapper nonzero: the scenario requires `status=fail`, a retained failure
  report, and the absence of `status=pass`, then fails the SSpec. This validates
  fail-closed classification without allowing unavailable runtime to pass.

## Current blocker

The last recorded current-source native build stopped before QEMU launch.
Unavailable runtime, a Rust seed, a stale artifact, a missing crop, or
uncorrelated serial output cannot promote this manual to PASS.

Broad multi-window/app-content coverage, drag/minimize/taskbar-restore coverage,
and the 30-pair latency/performance row remain owned by their focused WM
scenarios; this font/input scenario does not claim REQ-3, REQ-4, REQ-6,
NFR-4, or NFR-6.
