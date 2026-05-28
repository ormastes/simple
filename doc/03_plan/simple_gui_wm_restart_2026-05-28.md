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
- `doc/04_architecture/simple_gui_stack.md`
- `doc/04_architecture/gui_layer_contract.md`
- `doc/04_architecture/shared_wm_stack.md`
- `doc/04_architecture/cross_platform_wm.md`
- `doc/03_plan/wm_ui_export_plan.md`

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
- `test/unit/app/ui/ipc_protocol_spec.spl`
- `test/unit/app/ui/ipc_spec.spl`
- `test/unit/app/ui/async_ipc_spec.spl`

What changed:
- IPC protocol parser/builders were made public where tests and backend modules import them.
- IPC input is normalized for over-escaped JSON strings.
- `extract_json_field` now searches keys with interpolation (`"\"{field_name}\""`) and scans to the following colon, avoiding bad offsets from chained quoted-key construction.
- IPC specs were updated away from stale matcher forms.
- Scratch probe files were deleted.

Verification already passed after this slice:

```bash
SIMPLE_LIB=src bin/simple check src/app/ui.ipc/protocol.spl test/unit/app/ui/ipc_protocol_spec.spl test/unit/app/ui/ipc_spec.spl test/unit/app/ui/async_ipc_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/app/ui/ipc_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/app/ui/ipc_protocol_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/app/ui/async_ipc_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/app/ui/gui_event_pipeline_contract_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/app/ui/tauri_backend_spec.spl --mode=interpreter --clean
```

Additional restart evidence added after that commit:

```bash
SIMPLE_LIB=src bin/simple check src/os/compositor/host_compositor_entry.spl test/unit/os/compositor/host_compositor_entry_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/os/compositor/host_compositor_entry_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/os/compositor/simple_web_window_renderer_spec.spl --mode=interpreter --clean
```

The host WM handle now records the selected host backend and exposes the shared
content renderer contract. The focused spec proves Browser, Electron, and Tauri
shared-WM handles all report `simple_web` as the window-content renderer.
The WM app-content renderer also uses a WM-local Simple Web stylesheet and the
host compositor spec proves Terminal window content flows through Simple Web
into Engine2D pixel colors before compositor blit.

## Remaining Work

1. Replace remaining SimpleOS GUI probe-only coverage with a real shared WM path where feasible.
2. Add SimpleOS adapter proof for display/input/event delivery, preferably with QEMU smoke coverage.
3. Add macOS validation for Cocoa-backed host WM when a macOS host is available.
4. Update architecture docs if implementation reveals a different adapter boundary.

## Known Blockers

- `jj status` has failed or hung in this repo because of repository metadata problems. Use scoped `git` fallback if needed.
- GitHub SSH fetch/push failed with `Permission denied (publickey)`.
- Rebase against `origin/main` was blocked by unrelated dirty worktree changes.
- Live SimpleOS QEMU GUI proof was not completed; earlier system spec timed out around 120 seconds.
- Real macOS Cocoa proof was not possible on this Linux host.

## Scoped Commit Discipline

The worktree contains many unrelated dirty files. Do not stage broad changes. For the IPC slice, stage only:

```bash
git add src/app/ui.ipc/protocol.spl \
  test/unit/app/ui/ipc_protocol_spec.spl \
  test/unit/app/ui/ipc_spec.spl \
  test/unit/app/ui/async_ipc_spec.spl
```

Then attempt:

```bash
git commit -m "fix: stabilize shared ipc event parsing"
git fetch origin
git rebase origin/main
git push origin HEAD:main
```

If fetch/push/rebase still fail, record the exact blocker and leave the local commit intact.
