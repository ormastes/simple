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

The new system spec is a bounded live WM input smoke for
`examples/09_embedded/simple_os/arch/x86_64/wm_input_test_entry.spl`. It builds the
standalone input-test kernel, boots it under `qemu-system-x86_64` when the
kernel exists, and asserts the serial input markers for init, focus click,
drag to `444,252`, `[PASS] wm_input_test_entry`, and `TEST PASSED`.

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
- 2026-05-28 follow-up: the entry now initializes PCI before painting the BGA
  framebuffer, emits `[wm-input-test] framebuffer marker OK`, and the spec
  decodes the QMP PPM to assert the expected background, title-bar, and dragged
  window marker pixels.
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
src/compiler_rust/target/debug/simple check src/os/qemu_runner_part1.spl src/os/qemu_runner_part2.spl test/03_system/gui/arm64_wm_qemu_contract_spec.spl test/01_unit/os/qemu_runner_extended_spec.spl
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
