# RV64 SimpleOS WM font and input evidence

Status: **BLOCKED — no live RV64 font or input PASS is claimed.**

This is the RV64 QEMU dev-board lane for
`examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl`. It is
separate from both the x86_64 SimpleOS gate and the generic RV64 nonblank
display-smoke gate.

## Required production proof

1. Boot the current pure-Simple
   `build/os/simpleos_riscv64_display_smoke.elf`.
2. Load `/SYS/FONTS/NOTOSANS` with exactly 1,708,408 bytes and SHA-256
   `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
   The guest must emit this exact marker:
   `[rv64-font-evidence] guest_path=/SYS/FONTS/NOTOSANS asset_bytes=1708408 asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081 route=shared-wm-draw-ir component_id=taskbar-clock`.
   Any `rv64-font-evidence-unavailable` or
   `rv64-input-evidence-unavailable` marker rejects the run before PASS.
3. Render the taskbar clock through
   `SharedWmScene -> DrawIrComposition -> Engine2D`.
4. Inject a keyboard event and a pointer press/release through QMP
   `input-send-event` into RV64 VirtIO input devices.
5. Correlate each new guest input sequence across device IRQ, WM state, and a
   later framebuffer generation: keyboard sequence is above the pre-injection
   baseline and its frame generation is above the desktop-present revision;
   pointer sequence is later than keyboard and its frame generation is later
   than keyboard's.
6. Capture the RV64-only `right56,bottom48` RGB crop (8,064 bytes), require its
   exact pinned SHA-256, flip `crop[0]` in a copy, and prove the same oracle
   rejects the copy. The crop is exactly the final 48 rows and final 56 pixels
   per row of the QMP PPM, never a serial-derived or x86_64 crop.

The crop hash must come from a fresh RV64 QMP capture. The x86_64 crop hash is
not admissible.

## Shared font primary flow

1. Load the pinned multilingual font manifest
2. Accept exact-face-bound simple-script shaping
3. Prepare one shared font batch for 2D and 3D
4. Emit the selected font composite program and plan compilation
5. Prove native submission and device readback

The same live scenario traces and rejects boundary failures with:

1. Trace the production font and event boundary
2. Submit the boundary output to its canonical consumer
3. Correlate visible pixels and input with one frame identity
4. Reject disconnected stale or replayed evidence

## Current blockers

- The RV64 entry does not mount the pinned font asset and emits
  `rv64-font-evidence-unavailable`.
- The RV64 entry consumes UART shortcuts, not VirtIO keyboard/pointer events,
  and emits `rv64-input-evidence-unavailable`.
- `RV64_WM_FONT_REGION_EXPECTED_SHA256` is intentionally empty until a genuine
  RV64 crop is captured.
- No qualifying current-source RV64 ELF exists in the worktree, so QEMU was
  not launched during this static design pass.

## Commands

Parser and corruption calibration only:

```bash
sh scripts/check/check-rv64-display-smoke-qmp-evidence.shs --self-test-wm-font-input
```

After the font and VirtIO input routes are implemented, build once and collect
the live calibration result:

```bash
bin/simple os build --scenario=riscv64-display-smoke
RV64_DISPLAY_SMOKE_BUILD=0 \
  scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input
```

Pin the reported RV64 crop SHA-256, then rerun once with
`RV64_WM_FONT_REGION_EXPECTED_SHA256` set. PASS requires exact font identity,
the exact guest marker, absence of unavailable markers, the exact crop,
corrupt-copy rejection, and both keyboard and pointer correlation rows.
