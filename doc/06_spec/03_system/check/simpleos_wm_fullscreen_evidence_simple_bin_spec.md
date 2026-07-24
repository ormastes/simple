# SimpleOS WM Fullscreen Evidence Binary Contract

> **Current result: BLOCKED / no live QEMU PASS (2026-07-24).**
> Executable source:
> `test/03_system/check/simpleos_wm_fullscreen_evidence_simple_bin_spec.spl`.
> This manual is synchronized by hand because pure-Simple docgen was
> unavailable; it does not claim generated zero-stub evidence.

## Purpose

This SSpec checks the fail-closed source and launcher contract around
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`. Static source
assertions are supporting evidence. Only a fresh successful wrapper run can
prove guest font pixels and correlated QEMU input.

The focused font/input scenario uses the shared steps:

- Load the pinned multilingual font manifest
- Accept exact-face-bound simple-script shaping
- Trace the production font and event boundary
- Prepare one shared font batch for 2D and 3D
- Emit the selected font composite program and plan compilation
- Submit the boundary output to its canonical consumer
- Correlate visible pixels and input with one frame identity
- Prove native submission and device readback
- Reject disconnected stale or replayed evidence

## Primary flow

1. Load the pinned multilingual font manifest.
2. Require the deterministic guest path `/SYS/FONTS/NOTOSANS`, byte length
   `1708408`, and SHA-256
   `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
3. Boot only the production x86_64 `gui_entry_desktop.spl` with an accepted
   pure-Simple self-hosted binary. Its live `SharedWmScene` snapshot is rendered
   through Draw IR and the `Engine2dWmFrameExecutor`; the guest emits the pinned
   taskbar-clock `route=shared-wm-draw-ir` marker rather than a private font path.
4. Derive framebuffer address, dimensions, pitch, format, and size only from
   the guest `[scanout-evidence]` marker.
5. Capture baseline, maximized, and restored frames through QMP `pmemsave`;
   extract the 8,064-byte taskbar-clock RGB crop from that device-origin
   baseline.
6. Correlate F11 maximize/restore through guest IRQ, WM state, and frame
   generation with strictly increasing `input_seq` values.
7. Move to the center of the guest-reported restored-window titlebar and press
   the left button. Accept only `window_focus` or `window_drag_begin` when the
   command window equals the positive focused window.
8. Release the left button. Require a newer sequence, the same focused window,
   `command=ignored`, `handled=false`, and a positive frame generation.
9. Copy the crop, XOR exactly one byte, preserve its 8,064-byte length, compute
   its SHA-256 with the wrapper’s existing hash helper, and require the shared
   crop oracle to reject it before PASS.
10. Retain only valid PPM captures: maximize must change more than 4,096 scanout
    bytes and restore must reproduce the baseline hash. The evidence record names
    all three PPM magic statuses and the QMP `pmemsave` device origin.

## Fail-closed rows

- Rust seed paths, symlinks resolving to a seed, seed-identifying version
  output, and failed version probes reject before QEMU.
- Missing or stale kernel/disk artifacts, invalid scanout metadata, QMP errors,
  serial-only markers, missing guest correlations, blank captures, duplicate
  hashes, and crop-oracle mismatches remain failures.
- A current-source kernel build uses the same unoptimized WM target profile as
  the canonical QEMU runner, runs under a 900-second host watchdog, writes to a
  candidate ELF, validates ELF64 little-endian identity and x86_64 machine
  type, and only then atomically admits it. A
  timeout removes the candidate while retaining `native-cache` for the next
  bounded attempt. Reuse also requires the admission sidecar to match the
  wrapper, pure-Simple compiler, build profile, full source-content revision,
  and recomputed ELF SHA-256. The source revision is checked again before
  promotion so concurrent edits cannot admit a mixed-source ELF. The default
  image is then recorded as `built-from-admitted-kernel`. If an externally
  validated kernel is used to build the default image, it is recorded instead
  as `built-from-external-elf-validated`. External image overrides must have
  the canonical SimpleOS FAT32 BPB/header and pass a host FAT checker before
  being labeled `external-fat32-validated`. External kernel overrides receive
  only ELF64 little-endian x86_64/hash validation and remain labeled
  `external-elf-validated`; they are not claimed as current-source builds.
- A closed QMP connection fails the capture; maximize, restore, press, and
  release markers must be strictly newer than their preceding guest `input_seq`,
  so replayed markers cannot satisfy the correlation.
- The deliberate corrupt crop must exist, retain the expected byte count,
  produce a valid SHA-256 different from the unmodified crop, and be rejected.
  A missing corrupt file cannot count as successful calibration.

## Current retained result

Command attempted:

```sh
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Result: `simpleos_wm_fullscreen_reason=wm-simple-web-build-failed`.
The self-hosted native build exceeded the requested 300-second timeout and was
terminated after roughly 13 minutes. It produced no fresh kernel, QEMU launch,
serial markers, framebuffer, font crop, pointer evidence, or corrupt-copy
calibration.

Retained artifacts:

- `build/simpleos_wm_fullscreen_evidence/evidence.env`
- `build/simpleos_wm_fullscreen_evidence/native-build.out` (0 bytes)
- `doc/09_report/simpleos_wm_fullscreen_evidence_2026-07-24.md`

The bounded admission repair was not promoted to live QEMU evidence in the
isolated x86 worktree: its only pure-Simple executable exited 139 before the
focused contract ran. No Rust seed or external artifact was substituted.

## Status matrix

| Row | Status | Required evidence |
|---|---|---|
| Pure-Simple launcher provenance | Source-covered | Fresh executable hash/version still required in live PASS |
| ELF/image admission contract | Source-covered | Executable cases added; current pure-Simple test runner exits 139 |
| Pinned guest font path/length/hash | Source-covered | Guest marker and device crop missing |
| Dynamic QMP `pmemsave` crop | BLOCKED | QEMU did not launch |
| F11 IRQ/state/frame correlation | BLOCKED | No guest execution |
| Pointer press command/focus match | BLOCKED | No guest execution |
| Pointer release ignored/same-focus match | BLOCKED | No guest execution |
| One-byte corrupt-copy rejection | BLOCKED | No real crop to copy |

Resume after a runnable current pure-Simple compiler is staged:

```sh
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
SIMPLE_LIB=src bin/simple test test/03_system/check/simpleos_wm_fullscreen_evidence_simple_bin_spec.spl --mode=interpreter --clean
```
