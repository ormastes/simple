# Simple GUI / WM Restart Plan - 2026-05-28

## Goal

Resume the Simple GUI and window-manager convergence work without rediscovering state.

Target stack sanity:

```text
Simple GUI app
  -> host-backed simple WM
  -> host backend: browser / Electron / Tauri / Cocoa
  -> Simple web renderer
  -> Simple 2D renderer
  -> GPU or platform backend: CUDA / Metal / software / other

SimpleOS-backed simple WM
  -> same WM model and most rendering/event code
  -> SimpleOS framebuffer/input/storage adapters
```

Expected architecture answer: host WM and SimpleOS WM should share the WM model, scene/tree, event normalization, Simple web renderer bridge, and Simple 2D renderer path. They should differ only at the platform adapter boundary: host windows/events versus SimpleOS framebuffer/input/device services. If a feature works in the host WM and only uses shared contracts, it should be portable to SimpleOS after the SimpleOS adapter provides equivalent display, input, timing, storage, and process hooks.

Related docs:
- `doc/04_architecture/ui/simple_gui_stack.md`
- `doc/04_architecture/compiler/graphics/gui_layer_contract.md`
- `doc/04_architecture/os/shared_wm_stack.md`
- `doc/04_architecture/platform/cross_platform_wm.md`
- `doc/03_plan/wm_ui_export_plan.md`
- `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md`

## 2026-07-05 Redesign Plan: Real App Process WM

The current filesystem-launched showcase frame bridge is a transition proof,
not the final WM/app contract. The redesign target is a shared GUI backend
interface where the same app source can run in either native-host mode or
WM-client mode without source changes. Rebuilds or script-mode launch flags are
allowed, but the app identity stays the filesystem source/binary path and the
WM always launches the app as a separate process on both host platforms and
SimpleOS.

### Required end state

1. **Same app source, different launch backend.** A GUI app selects one backend
   at launch: native host backend, host WM-client backend, or SimpleOS
   WM-client backend. App code calls the same GUI API in all modes.
2. **Separate process ownership.** The WM starts apps from filesystem paths,
   tracks PID/app id/window ids/taskbar state, receives lifecycle messages, and
   can terminate the child. No showcase/widget code is embedded in the WM.
3. **Bidirectional GUI protocol.** The WM/app protocol must carry
   `create_window`, `frame_update`/damage, `pointer_event`, `keyboard_event`,
   `text_input`, `wheel`, `focus`, `resize`, `close`, `kill`, `theme_update`,
   and `taskbar_update` messages. Content clicks are routed to the child with
   window-local coordinates; chrome/taskbar clicks stay WM-owned.
4. **Taskbar as a model object.** Taskbar rendering consumes a shared taskbar
   object: app id, pid, title, icon/thumbnail, focused/minimized/running state,
   progress/badge, and close/restore actions. Rect-only taskbar drawing is not
   sufficient for completion.
5. **Theme parity.** WM chrome and app surfaces consume the same theme token
   source used by Simple GUI/CSS. The WM may render the theme through pixels,
   Draw IR, HTML/CSS, or GPU commands, but the resolved colors/states must be
   shared and testable.
6. **Host modes.** Host WM supports three presentation modes:
   full-screen desktop, windowed desktop, and taskbar-only/native-window mode.
7. **SimpleOS mode.** SimpleOS uses one presentation mode for this lane:
   full-screen WM desktop.

### GPU/offload policy

GUI app rendering is allowed to be offloaded to GPU in the child process. The
WM protocol must therefore support both:

- CPU/shared-memory or file-backed frame transport for bootstrap and tests.
- GPU-backed transport where available, such as platform texture/surface
  sharing or device-local frame handles, with typed fallback diagnostics when
  hardware/runtime support is missing.

The WM compositor may also GPU-compose child surfaces and chrome. The key rule
is ownership, not CPU-only rendering: the child owns app rendering, the WM owns
composition/input/taskbar/lifecycle, and the protocol carries enough
capability metadata to choose GPU or fallback transport without changing app
source.

### Implementation phases

1. **Contract first.** Define shared structs and message encoding for app
   process lifecycle, window creation, frame updates, input events, taskbar
   state, theme updates, capabilities, and kill/close acknowledgements.
2. **Backend adapter.** Add a GUI backend interface that native host and
   WM-client launch modes both implement. Existing widget/showcase source must
   call this interface rather than branching into separate UI code.
3. **Host process transport.** Implement host WM/app IPC with filesystem source
   launch, child PID tracking, event forwarding, frame update acknowledgement,
   and process kill. Use CPU frame transport first, then add GPU transport as a
   capability-gated optimization.
4. **Event routing.** Normalize Winit/host input into WM events, hit-test
   chrome/taskbar/content, forward content events to the child, and require
   updated frames after state-changing input.
5. **Taskbar/theme polish.** Replace primitive taskbar rectangles with the
   shared taskbar model renderer and shared theme states: focused, hover,
   pressed, minimized, progress/badge, close/restore.
6. **SimpleOS process transport.** Port the same protocol to SimpleOS process
   communication using the optimized SimpleOS IPC/channel path. Keep the wire
   model compatible with the host transport while allowing SimpleOS-specific
   zero-copy or GPU/framebuffer optimizations below the adapter.
7. **Final QEMU full-screen evidence.** Completion is not host-only. The final
   acceptance lane boots SimpleOS in QEMU into full-screen WM mode, launches the
   showcase app from the SimpleOS filesystem as a separate process, routes
   pointer/keyboard events through the WM into the child, receives frame
   updates, shows the shared taskbar/theme, kills/closes the child on command,
   and captures framebuffer plus serial markers as release evidence.

### System-test additions

- Host native launch vs host WM-client launch proves the same app source path
  and same GUI API entrypoint are used.
- Host WM interaction test sends drag, click, keyboard, wheel, focus, taskbar
  restore/minimize, close, and child-content click events; assertions must
  include local-coordinate forwarding and child frame update evidence.
- Taskbar/theme visual tests assert non-placeholder taskbar model fields and
  shared theme token application.
- GPU capability tests assert GPU transport is allowed and selected when
  available, while CPU fallback reports typed capability diagnostics.
- SimpleOS QEMU full-screen system test is the final gate for this redesign.

## Completed In This Session

Committed fixes:
- `4424e891af` - share Simple web WM rendering path.
- `15d0e78194` - bootstrap graphical host WM handles.
- `376b2875b4` - align shared WM entrypoint matrix.
- `db62cea7f2` - add host WM tick loop.
- `9eb7c53132` - render host WM windows with Simple web.
- `9d337ba538` - keep SimpleOS desktop shortcut flow reachable.
- `23a9625617` - wire Cocoa hosted backend to native SFFI symbols.
- `92737a5854` - wire GUI IPC events through UI state.

Verified during the session:
- Host compositor / Simple web window renderer / shared WM specs passed.
- Cocoa hosted backend source contract passed on Linux.
- Desktop shortcut source-contract test passed.
- GUI event pipeline contract and Tauri backend tests passed.

## Completed IPC Stabilization Slice

Committed as `ea48a3470a` (`fix: stabilize shared ipc event parsing`):
- `src/app/ui.ipc/protocol.spl`
- `test/01_unit/app/ui/ipc_protocol_spec.spl`
- `test/01_unit/app/ui/ipc_spec.spl`
- `test/01_unit/app/ui/async_ipc_spec.spl`

What changed:
- IPC protocol parser/builders were made public where tests and backend modules import them.
- IPC input is normalized for over-escaped JSON strings.
- `extract_json_field` now searches keys with interpolation (`"\"{field_name}\""`) and scans to the following colon, avoiding bad offsets from chained quoted-key construction.
- IPC specs were updated away from stale matcher forms.
- Scratch probe files were deleted.

Verification already passed after this slice:

```bash
SIMPLE_LIB=src bin/simple check src/app/ui.ipc/protocol.spl test/01_unit/app/ui/ipc_protocol_spec.spl test/01_unit/app/ui/ipc_spec.spl test/01_unit/app/ui/async_ipc_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/app/ui/ipc_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/01_unit/app/ui/ipc_protocol_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/01_unit/app/ui/async_ipc_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/01_unit/app/ui/gui_event_pipeline_contract_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/01_unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean
```

Additional restart evidence added after that commit:

```bash
SIMPLE_LIB=src bin/simple check src/os/compositor/host_compositor_entry.spl test/01_unit/os/compositor/host_compositor_entry_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/01_unit/os/compositor/simple_web_window_renderer_spec.spl --mode=interpreter --clean
```

The host WM handle now records the selected host backend and exposes the shared
content renderer contract. The focused spec proves Browser, Electron, and Tauri
shared-WM handles all report `simple_web` as the window-content renderer.
The WM app-content renderer also uses a WM-local Simple Web stylesheet and the
host compositor spec proves Terminal window content flows through Simple Web
into Engine2D pixel colors before compositor blit.

Additional SimpleOS GUI proof added after the restart evidence:

```bash
SIMPLE_LIB=src bin/simple check src/os/compositor/host_compositor_entry.spl test/01_unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl
SIMPLE_LIB=src bin/simple test test/01_unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl --mode=interpreter --clean
```

The focused SimpleOS GUI adapter spec no longer stops at display/content-renderer name
probes: it delivers a bridge create-window request and framebuffer render
through the shared `HostCompositor` path, then asserts the shared window list
preserves the app content while the captured framebuffer contains WM chrome
before presentation.

Additional live QEMU input proof lane added after the adapter proof:

```bash
SIMPLE_LIB=src bin/simple check test/03_system/gui/wm_input_qemu_smoke_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_input_qemu_smoke_spec.spl --mode=interpreter --clean --format json
```

The system spec is a bounded live WM input smoke for
`examples/09_embedded/simple_os/arch/x86_64/wm_input_test_entry.spl`. It builds the
standalone input-test kernel, boots it under `qemu-system-x86_64` when the
kernel exists, and asserts serial markers for init, focus click, structured
focus command routing, titlebar button click, titlebar text input edit, CSS
pixel scale, structured drag command routing to `444,252`,
`[PASS] wm_input_test_entry`, and `TEST PASSED`.

Current result on this Linux host:

- `check` passes for the new spec.
- QEMU is installed at `/usr/bin/qemu-system-x86_64`.
- 2026-05-28 follow-up: the freestanding link blocker is fixed by removing the
  file-scope data symbols from `wm_input_test_entry.spl`; serial port constants
  are now local constant-return helpers and the serial marker path no longer
  needs mutable file-scope state.
- `SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_input_qemu_smoke_spec.spl --mode=interpreter --clean --format json`
  now passes `3/3` in 14962 ms and boots the live QEMU input smoke through the
  init/focus/drag/pass serial-marker path plus QMP framebuffer capture.
- 2026-06-13 follow-up: the entry emits structured markers for
  `[wm-input-test] focus command_kind=focus_window window_id=1`,
  `[wm-input-test] titlebar_button_click action=close window_id=1`,
  `[wm-input-test] text_input_edit window_id=1 field=search before='' after='abc'`,
  `[wm-input-test] css_pixels viewport=1024x768 browser=320x202 scale=1`, and
  `[wm-input-test] drag command_kind=move_window window_id=1 from=320,180 to=444,252`.
  The x86_64 Multiboot header is serial-safe for this smoke lane, the entry uses
  `spl_start` to avoid a boot-entry symbol conflict, and the freestanding entry
  no longer imports PCI just to paint its deterministic framebuffer marker.
- 2026-06-13 verification: `SIMPLE_LIB=src bin/simple test test/03_system/gui/wm_input_qemu_smoke_spec.spl --no-cache`
  passed `3/3` in 8427 ms with the structured markers and QMP framebuffer
  capture.
- 2026-05-28 harness fix: QEMU stale cleanup now scopes `pkill -f` to
  `qemu-system.*<identity>` patterns so cleanup no longer kills the shell/test
  command that mentions the same log path.

Additional non-x86 GUI source-contract coverage:

```bash
bin/simple check test/03_system/gui/arm64_wm_qemu_contract_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/gui/arm64_wm_qemu_contract_spec.spl --mode=interpreter --clean --format json
```

The ARM64 contract spec ties `doc/07_guide/platform/simpleos/simpleos_arm64_wm_qemu.md`
to `examples/09_embedded/simple_os/arch/arm64/wm_entry.spl` and
`examples/09_embedded/simple_os/arch/arm64/wm_entry_io.spl`. It checks that the documented
`qemu-system-aarch64`/`ramfb` command, `aarch64-unknown-none` target, output
ELF path, fw_cfg MMIO address, `etc/ramfb` selector path, and acceptance serial
markers are present in the guide and source. This prevents drift in the non-x86
WM lane while keeping the live proof status honest: it is source/guide contract
coverage, not an ARM64 QEMU boot result.

Additional ARM64 host-readiness and canonical target contract coverage:

```bash
sh -n scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs
sh scripts/check/check-simpleos-arm64-wm-qemu-readiness.shs
src/compiler_rust/target/debug/simple check src/os/_QemuRunner/runner_targets.spl src/os/_QemuRunner/os_build_run.spl test/03_system/gui/arm64_wm_qemu_contract_spec.spl test/01_unit/os/qemu_runner_extended_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/03_system/gui/arm64_wm_qemu_contract_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/01_unit/os/qemu_runner_extended_spec.spl --mode=interpreter --clean --format json
```

Current result on this Linux host:

- The readiness probe reports `/usr/bin/qemu-system-aarch64`, `virt`, `ramfb`,
  and the bounded headless dry-run parse as ready.
- The ARM64 contract spec now passes `7/7` and asserts the guide/source
  markers, the host-runnable `get_arm64_wm_qemu_target()` build/run contract,
  the named `arm64-wm-ramfb` scenario command contract, runner CLI commands,
  WM-specific serial acceptance markers, and a 120s scenario test timeout.
- The extended QEMU runner spec now passes `25/25` and asserts the ARM64 WM
  target uses `build/os/generated`, `src/os`, and `examples/09_embedded/simple_os`, plus
  `SIMPLE_BOOTSTRAP=1`, `SIMPLE_LIB="$(pwd)/src"`, and
  `SIMPLE_ALLOW_FREESTANDING_STUBS=1`; it also proves
  `get_scenario("arm64-wm-ramfb")` resolves to the WM target and QEMU command.
- This is still a contract/readiness slice, not a successful ARM64 WM boot,
  ramfb configuration, or framebuffer capture.

## Remaining Work

2026-06-05 QEMU/GTK capture refresh:

1. The canonical real-QEMU WM capture command is now:
   `QEMU_AUTO_LAUNCH_SIMPLEOS_DESKTOP=1 timeout 180 sh scripts/check/check-qemu-gtk-wm-capture-evidence.shs`.
   The wrapper runs from the repository root, launches the SimpleOS desktop
   through `src/app/test/simpleos_desktop_qmp_launch.spl`, captures a live QMP
   screendump, and chains the host GTK/GL exact-scene baseline through
   `scripts/check/check-gtk-gl-wm-scene-bitmap-evidence.shs`.
2. Latest evidence is
   `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-05.md`: live QEMU bitmap
   capture passes with `786432` pixels, `0` sample mismatches, `0` full-scene
   mismatches, and host GTK/GL scene mismatch count `0` with
   `blur/tolerance used: false`.
3. The QEMU guest now emits
   `[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=...
   iterations=16 timing_unit=tsc scope=simple-vga-paint`, and the wrapper pairs
   that guest Simple paint timing with the host GTK/GL baseline. The 2026-06-05
   report records `qemu-side perf status: pass` and
   `qemu-side perf release blocker: none`.

2026-06-05 layered GUI/WebRenderer/Engine2D parity refresh:

1. `scripts/check/check-layered-simple-gui-web-engine2d-bitmap-evidence.shs`
   now passes for `image_taskbar_command` and `toolbar_modal_grid` across
   Node, Bun, and Electron GUI lanes.
2. Latest evidence is
   `doc/09_report/layered_simple_gui_web_engine2d_bitmap_evidence_2026-06-05.md`:
   every lane reports `mismatch_count=0`, `blur_or_tolerance_used=false`, and
   Electron writes captured ARGB for both GUI scenes.
3. The Electron Engine2D wrapper now pins Chromium software/offscreen capture
   flags on headless Linux after `UnknownVizError` was observed in the default
   GPU-backed offscreen path. This keeps the exact bitmap policy and does not
   introduce blur or tolerance.

2026-06-05 production Electron/Tauri/Chrome/WebRenderer parity refresh:

1. `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` now
   requires live Tauri/WebKitGTK and Chrome/Chromium surface captures; Tauri or
   Chrome `unavailable` rows no longer satisfy the production parity gate.
2. Latest evidence is
   `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-05.md`:
   Electron matrix and layout manifest pass, Tauri live capture passes `18/18`
   rows with `0` failures and `0` mismatches, Chrome live capture has `0`
   mismatches, `no_fake_capture=true`, and `blur_or_tolerance_used=false`.
3. The pure Simple backend row in the same report passes with
   `production_gui_web_renderer_parity_backend_exact=true` and
   `production_gui_web_renderer_parity_backend_cpu_simd_different_pixels=0`.

2026-06-05 SimpleOS hardening matrix refresh:

1. `scripts/check/check-simpleos-hardening-evidence-matrix.shs` now points at
   the current QEMU/GTK, layered GUI/WebRenderer/Engine2D, CPU SIMD, shared
   WM, RV64 display-smoke QMP, and latest available production GUI/WebRenderer
   parity evidence reports unless a caller overrides the report paths.
2. Latest matrix evidence is
   `doc/09_report/simpleos_hardening_evidence_matrix_current_2026-07-02.md`:
   all `10/10` artifact rows pass, including the QEMU host counterpart, GUI
   SMF artifact contract, live MDI framebuffer rows, RV64 display-smoke QMP,
   and production Electron/Tauri/Chrome/WebRenderer parity.
3. The aggregate matrix status is now `pass`: the QEMU guest Simple paint
   marker supplies `simple_frame_cycles` and `iterations`, while the host
   GTK/GL baseline supplies the GTK timing field. The release gate is
   `guest-simple-frame-plus-host-gtk-baseline`.

2026-05-29 parallel restart expansion:

1. Use `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md` as the active
   lane checklist for the resumed renderer restart objective.
2. Keep Engine2D CPU/Vulkan, pure Simple web/Tauri, 2D UI layer, TUI/Simple
   IDE, Android GUI, iOS GUI, browser, and macOS ARM64 graphics evidence
   separate until each lane has focused commands and direct proof.
3. Do not mark the overall restart complete while any lane only has inferred
   evidence, missing platform proof, or a platform-unavailable note without a
   tracking entry.

2026-05-29 interrupted continuation from
`rollout-2026-05-29T06-34-21-019e7270-e325-71c3-8c7d-ec533ba14866.jsonl`:

1. Resume the GUI size/performance lane only after a fresh dirty-worktree audit.
2. Inspect the minimized renderer native-build inputs and record the exact
   source roots used by the current benchmark artifact.
3. Test narrower native-build source roots only if the runtime entry closure
   still includes the required renderer, WM, and platform adapter paths.
4. Regenerate the GTK size/speed report with complete raw rows before updating
   any ratio or summary text.
5. Keep the GTK comparison separate from shared web-render API refactoring; do
   not mix benchmark/report changes with renderer boundary changes in one
   commit.
6. Before commit, rerun the focused GUI/native-build checks and record the
   exact command, artifact path, binary size, startup/runtime timing, and any
   unavailable GTK speed reason.

Existing GUI/WM continuation:

1. Add macOS validation for Cocoa-backed host WM when a macOS host is available.
2. Promote the ARM64 target-contract/readiness lane into a live QEMU boot/capture
   lane when the ARM64 kernel compile, ramfb configuration, and capture path are
   production-ready.
3. Update architecture docs if implementation reveals a different adapter boundary.

## Known Blockers

- GitHub SSH fetch/push failed with `Permission denied (publickey)`.
- The 2026-05-29 GUI size/perf session was interrupted while report
  regeneration was running. Treat any partial report output as invalid until the
  benchmark is rerun and the raw rows are present.
- The current live SimpleOS GUI proof is a bounded x86_64 WM input/framebuffer
  smoke. It proves the focused QEMU lane, shared compositor adapter path, and
  marker pixels, but not a full desktop session or multi-architecture GUI run.
- The 2026-06-05 QEMU desktop capture proves live QMP screendump pixels and
  host GTK/GL exact-scene parity for the focused x86_64 desktop lane. It still
  does not prove guest-side Simple-vs-GTK performance until the QEMU guest emits
  the required `[desktop-e2e] qemu-perf sample_origin=qemu-guest ...` marker.
- ARM64 WM coverage is currently guide/source, host-readiness, and canonical
  QEMU target/command contract coverage only. It proves this host has
  `qemu-system-aarch64` with `virt` and `ramfb`, and that the runner can build
  the expected ARM64 WM command, not that the ARM64 kernel has compiled, booted,
  configured ramfb, or rendered a captured frame in this environment.
- Real macOS Cocoa proof was not possible on this Linux host.

## Scoped Commit Discipline

The worktree contains many unrelated dirty files. Do not stage broad changes. For the IPC slice, stage only:

```bash
git add src/app/ui.ipc/protocol.spl \
  test/01_unit/app/ui/ipc_protocol_spec.spl \
  test/01_unit/app/ui/ipc_spec.spl \
  test/01_unit/app/ui/async_ipc_spec.spl
```

Then attempt:

```bash
git commit -m "fix: stabilize shared ipc event parsing"
git fetch origin
git rebase origin/main
git push origin HEAD:main
```

If fetch/push/rebase still fail, record the exact blocker and leave the local commit intact.
