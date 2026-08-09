# Simple 2D Hardening - 4-Lane Parallel Sprint (2026-08-05)

## Objective
Harden SimpleOS Simple 2D on ARM QEMU and UNO Q native, and add a macOS/HVF lane for emulated execution parity checks, with Vulkan-backed paths where supported and a shared event/audio/font/render capture pipeline.

Execution window target: **1d 3h 24m** (planning, parser coverage, and gate hardening only on this host).

## Current completed work (reuse and do not duplicate)
- `src/os/gui/shortcut.spl` and `src/os/gui/input_event.spl` already provide shared key/mouse routing and modifier mapping for `ctrl`/`alt`/`shift` and action mapping.
- `scripts/check/check-simpleos-qemu-host-gpu-2d.shs` is already the canonical cross-ISA QEMU host GPU wrapper and has parser/self-test coverage.
- Existing lanes hold current blockers and acceptance tracking in:
  - `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_2d.md`
  - `doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`
  - `doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md`
  - `.spipe/simpleos-qemu-host-gpu-2d/state.md`
  - `.spipe/simpleos_macos_qemu_metal_gpu/state.md`
- Engine2D and ProcessingIR parity fixtures now have checked dispatch paths and shared metadata in source.
- Board command now has explicit `--self-test` reason coverage and fail-closed gating:
  - `scripts/check/check-simpleos-native-board-gpu-2d.shs`
- 2D showcase orchestration proof contract added:
  - `test/03_system/os/qemu/simpleos_2d_showcase_spec.spl`
  - `doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md`
- 2D showcase now also validates mouse/keyboard event entrypoints and animation hooks in shared WM host core source.

## What is still missing
- Fresh admitted Pure-Simple compiler/runtime and run-capable daemon artifacts on this host.
- Live evidence for:
  - Linux/Vulkan host rows: self-tests are complete, live PASS is blocked by compiler/runtime admission.
  - ARM64 QEMU Vulkan row: parser/self-test contracts are complete, live PASS is blocked by compiler/runtime admission.
  - RV64/board-adjacent transport closure: source and self-test contracts are complete, live PASS is blocked by compiler/runtime admission.
  - macOS HVF Metal row is non-runnable in this environment and remains emulation-only until delegated to an approved macOS host.
  - UNO Q board remains blocker and emits `board-not-connected` when no hardware is attached.
- Shared 1280x720 canonical DrawIR/parity artifact with deterministic event/audio/fame capture path is complete in source.
  - 4th-lane showcase currently validates the contract composition (DrawIR + input + audio + font) and writes a generated manual; a fresh live run is blocked by host/compiler readiness.
  - animation/interaction evidence is contract-level only on this host; live animation frame and event-latency proofs require a runnable native pass lane.

## Four parallel lanes (minimize duplicate logic)
All four lanes must use the same evidence fields and helper names:
`simpleos_native_board_gpu_*`, `simpleos_qemu_host_gpu_2d_*`, `SIMPLEOS_INPUT_EVENT`, `rv64_wm_*`, and `simpleos_io_audio_qemu_*`.

### Lane 1 — Linux/QEMU Vulkan hardening (Vulkan-backed)
- Scope: x86_64/aarch64/riscv64 live QEMU rows in existing wrapper.
- Deliverable:
  - one fresh wrapper run with `--self-test*` passing.
  - parser-gated freshness proof stays live-proof-blocked here by compiler/runtime admission.
  - exact DrawIR render + ProcessingIR readback parity against CPU oracle.
- Commands:
  - `SIMPLE_BIN=<pure-simple>` `sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test`
  - `SIMPLE_BIN=<pure-simple> SIMPLEOS_HOST_GPU_PROCESSING_BACKEND=vulkan sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs`

### Lane 2 — ARM QEMU and event contract proof (Vulkan-backed)
- Scope: ARM64 guest mapping/input pipeline proof on same wrapper path with strict event capture and key/mouse modifiers.
- Deliverable:
  - event fixture that emits mouse/click/key/ctrl/alt transitions and verified ordered receipts.
  - no duplicate keyboard/mouse parser logic; reuse `src/os/gui/shortcut.spl` and `src/os/gui/input_event.spl`.
  - lane output now uses shared checker matrix from `simpleos_2d_showcase_spec.spl`.
- Commands:
  - `SIMPLEOS_HOST_GPU_GUEST_ISAS=aarch64` with the canonical wrapper and fresh ARM64 probe artifacts.
  - `SIMPLE_BIN=<pure-simple> sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel`

### Lane 3 — macOS HVF row (emulator-only, non-runnable here)
- Scope: emulated macOS run path with current constraints.
- Status policy: tests/specs can be implemented and run only on macOS host; no in this lane host run is claimed.
- Emulator-readiness source contract now requires decoded and correlated
  move/down/drag/up/wheel coordinates and deltas, ordinary key delivery,
  distinct left/right Ctrl and Alt identities, one real audio
  submit/completion, twenty explicit submit/fence/device-readback animation
  frames, vector-font/capture integrity, 16.7 ms nearest-rank p95, 256 MiB
  maximum RSS, stable identity, and no fallback. TODO660 remains open until a
  source-matched prepared macOS host produces the live receipt.
- Deliverable:
  - run plan + test artifacts captured as `blocked`/`unsupported` with exact reasons, plus TODO list for runnable operators.
  - no synthetic pass records.
  - this host cannot run macOS-native acceleration and does not claim live PASS.
- Commands:
  - `SIMPLE_BIN=<admitted>` `SIMPLEOS_GPU_HOST_BIN=<metal-host-daemon>` `SIMPLEOS_HOST_GPU_GUEST_ISAS=aarch64 sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs`

### Lane 4 — UNO Q native board + 2D capture showcase (Vulkan-backed if available)
- Scope: board wrapper contract + capture showcase contract in a single lane.
- Deliverable:
  - fail-closed evidence for board command gating.
  - show-case contract in one scaffold (`simpleos_2d_showcase_spec.spl`) that validates:
    - draw/text/image path through DrawIR-linked contracts
    - pointer, keyboard, `ctrl` and `alt` modifier routing on shared shortcut contracts
    - audio/PCM transport and render path
  - board fail-closed reason matrix
  - typed physical provider boundary and composition-root admission are now in
    source; the QRB2210 Vulkan submit/fence/device-readback adapter exists but
    still needs the real SimpleOS kernel transport and board handles.
    Display/input/audio implementations remain missing, and all six canonical
    capabilities remain `port-unavailable` until their physical owners land.
- Commands:
  - `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict`
  - `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --self-test`
  - showcase run command captured in new spec/manual only (host-dependent; no emulation fallback accepted as production proof).

## Immediate parser-complete handoff items
- Run in a runnable host with admitted pure-Simple compiler/runtime:
  - `SIMPLE_BIN=<pure-simple> sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-metrics`
  - `SIMPLE_BIN=<pure-simple> sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel`
- On attached hardware:
  - `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict`
  - `sh scripts/check/check-simpleos-native-board-gpu-2d.shs --self-test`

## Completion matrix

| Lane | Done | Missing |
|---|---|---|
| Linux/QEMU Vulkan | ✅ parser/self-test + contract reuse | ⏸️ no fresh native PASS (compiler/runtime admission) |
| ARM64 QEMU + input/audio/font contracts | ✅ parser/self-test + shared source wiring | ⏸️ no fresh native PASS (compiler/runtime admission) |
| macOS HVF | ✅ parser/test harness exists | ⏸️ emulation-only here; no live native PASS |
| UNO Q board + showcase | ✅ board reason matrix, typed six-provider boundary, shared-route admission, fail-closed Vulkan primitive adapter, showcase spec/manual | ⏸️ no QRB2210 kernel Vulkan transport, display/input/audio providers, board runner, or attached UNO Q |

## Required acceptance additions before sprint complete
- Replace all placeholder status in `doc/06_spec/03_system/.../simpleos_qemu_host_gpu_2d_spec.md` and any generated manuals with live evidence rows.
- Keep one canonical row for `simpleos_native_board_gpu_status=blocked|unsupported|pass` and never report board pass from cached rows.
- Keep all lanes on shared DrawIR/Engine2D paths; no private renderer/audio/event forks.
- Keep perf gates fail-closed until measured evidence exists for latency and RSS (`simpleos_*_p95` + daemon/QEMU/combined maxima).
- Keep `TODO548`/`TODO577`/`TODO578` blocked state visible until one successful source-matched pure-Simple run sequence is done.

- Keep macOS row marked emulator-only in this host sprint.

### Pending actionable TODO

- Add explicit UNO Q board runner gating to this session handoff (TODO658): requires physical ABX00162/ABX00173 availability, a native-board pass contract, and retained artifacts under `build/test-artifacts/simpleos-native-board-gpu-2d/uno-q/`.
- Resume command template once admitted:
  - `SIMPLE_BIN=<admitted-simple> sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict`
- Keep `simpleos_native_board_gpu_status` and `simpleos_native_board_gpu_reason` explicit (`blocked`, `runner-not-yet-implemented`, `board-not-connected`, then `pass` when real evidence exists) and never infer pass from cached rows.

## Work output files
- [scripts/check/check-simpleos-native-board-gpu-2d.shs](/home/ormastes/dev/pub/simple/scripts/check/check-simpleos-native-board-gpu-2d.shs)
- [test/03_system/os/qemu/simpleos_2d_showcase_spec.spl](/home/ormastes/dev/pub/simple/test/03_system/os/qemu/simpleos_2d_showcase_spec.spl)
- [doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md](/home/ormastes/dev/pub/simple/doc/06_spec/03_system/os/qemu/simpleos_2d_showcase_spec.md)
- [doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md](/home/ormastes/dev/pub/simple/doc/03_plan/agent_tasks/simpleos_cross_host_qemu_board_gpu_2d_parity.md)
- [doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_2d.md](/home/ormastes/dev/pub/simple/doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_2d.md)
