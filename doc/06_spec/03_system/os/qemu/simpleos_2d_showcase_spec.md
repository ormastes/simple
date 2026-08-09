# SimpleOS 2D Showcase Evidence

Status: parser/contracts complete, live PASS is intentionally blocked on this host.

## Objective
Harden and validate the cross-platform SimpleOS 2D flow with shared DrawIR rendering, event routing, sound capture, and font rendering through a single 4-lane evidence contract.

## Scope
- Linux x86_64/aarch64/riscv64 host GPU rows (Vulkan-backed render path)
- ARM64 QEMU event/input route sharing
- macOS lane marked emulator-only in this environment
- UNO Q native board fail-closed contract
- DrawIR and ProcessingIR offload reuse from shared engine paths

## Evidence scripts and assertions used
- `scripts/check/check-simpleos-native-board-gpu-2d.shs --self-test`
- `scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test`
- `scripts/check/check-simpleos-io-audio-qemu.shs --self-test`
- `scripts/check/check-rv64-display-smoke-qmp-evidence.shs --self-test-wm-font-input`
- `test/03_system/os/qemu/simpleos_2d_showcase_spec.spl`

## Parser contract targets
- Board checker matrix validates:
  - missing board,
  - unsupported board,
  - runner-not-yet-implemented for boards without a runner,
  - board-not-connected when UNO Q is unattached, and
  - live-qrb2210-simpleos-runner-required-offline-preflight-only when UNO Q
    attachment is asserted at the dispatcher without live runner-owned evidence.
- The board self-test forces `SIMPLEOS_UNOQ_BOARD_ATTACHED` absent and emits an
  explicit `unattached_status=blocked`/`board-not-connected` row; it never
  flashes, probes, or claims a physical board.
- Host GPU checker validates pass row contract (Linux row pass + render backend matrix)
  and emits inactive macOS rows as `unsupported`, reason
  `requires-macos-host`, execution class `emulator-only`; no macOS row may be
  reported as `pass` by this Linux self-test.
- Audio checker validates keyboard/pointer/controller receipts and playback/capture non-silent traces.
- Host GPU metrics contract validates render sample count + p95 + RSS evidence (no hardcoded synthetic values).
- RV64 checker validates font route, marker parsing, and keyboard/pointer correlation.
- Showcase source contract validates DrawIR/event entrypoints plus keyboard modifier state routing (`alt_held`, `ctrl_held`) and host-side animation hooks (`web_animation_dirty_due`, `animation_frame_due`).

## Lane status at handoff
- Lane 1 (Linux/QEMU Vulkan): parser/self-test complete, live pass blocked by compiler/runtime admission.
- Lane 2 (ARM64/QEMU event): parser/self-test complete, live pass blocked by compiler/runtime admission.
- Lane 3 (macOS HVF): emulator-ready source contract decodes and correlates move/down/drag/up/wheel, ordinary keys, and distinct left/right Ctrl/Alt; requires one real audio submit/completion, twenty explicit submit/fence/device-readback animation frames, vector-font/capture integrity, p95 and maximum-RSS budgets, and no fallback. It remains emulator-only and cannot produce a live PASS on this Linux host.
- Lane 4 (UNO Q + showcase): parser/matrix complete; board pass intentionally blocked unless hardware is attached.

## What is done vs. still blocked
- ✅ Done:
  - 4-lane structure and artifacts exist.
  - Board fail-closed matrix reasons are explicit.
  - Linux QEMU rows are Vulkan-bound in parser evidence.
  - Host/event/audio/font marker contracts are checked from shared checker code.
- ⏸️ Still blocked:
  - Fresh native PASS on this host for Linux/QEMU/ARM64 rows because pure-Simple compiler admission/runtime still needs to be installed end-to-end.
  - macOS/uno-q native row execution cannot be completed on this host; macOS remains emulator-only here, and UNO Q is not attached.
    - On this host, macOS row must stay `unsupported` or `blocked` and must only be promoted after a prepared-macOS host run with native contracts.
    - TODO 658 owns the eventual board-attached UNO Q identity, download,
      fence, device-readback, and DrawIR parity proof. TODO 660 owns the
      source-matched prepared-macOS DrawIR-to-Engine2D-to-Vulkan receipt; this
      Linux host supplies static/unit evidence only. TODO 661 owns the complete
      animation/input/font/sound four-lane proof and keeps this host's macOS row
      parser/tests-only. TODO 664 keeps final session closure blocked until a
      fresh attached UNO Q run supplies native DrawIR+ProcessingIR and physical
      event, font, sound, frame-progress, identity, and artifact receipts.
      None of those TODOs is closed by this self-test.
  - No live animation frame counter proof yet in this environment (existing animation fixtures are contract-level only in this lane).

## TODO handoff once environment is runnable
- Run `SIMPLE_BIN=<pure-simple>` `scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-metrics` with live QEMU rows and record row-level p95/RSS as proof.
- Run `SIMPLE_BIN=<pure-simple>` `scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel` for ARM64 accel validation.
- Capture and attach live macOS HVF and UNO Q board proof from a matching host.
- Replace `Status` from parser/contracts to live PASS once all four lanes run.

## Human follow-up
- When a pure-Simple admission environment is available, run the same four specs without self-test flags and replace parser-only status with live evidence rows.
- Keep generated manuals and test artifacts as parser-to-live transitions, not synthetic passes.
