# Feature: wm-full-stack-demo

## Raw Request
`$sp_dev impl wm, event, audio harden plan specially wm`

## Task Type
feature

## Refined Goal
Deliver the first honest Linux/GLFW Simple WM vertical slice: normalized
window events route through WM chrome and GUI clients; GUI, Web, and Simple 2D
content reach the compositor through `WmContentFrame`; lifecycle/taskbar
mutations persist and release handles; button audio produces deterministic PCM.
Keep SDL2/SDL3, QEMU HDA, and QRB2210 as explicit fail-closed follow-on gates
using the same contracts.

## Acceptance Criteria
- AC-1: A bounded FIFO preserves normalized key, text, pointer, wheel, focus,
  and resize events separately, with generation handles and overflow evidence.
- AC-2: Unsupported window operations return explicit capability status, never
  fabricated success.
- AC-3: GUI, Web, and pixel-surface producers submit validated
  `WmContentFrame` values through one explicit content-kind/handle boundary.
- AC-4: The Linux GLFW lane shows a real non-black desktop frame and routes at
  least one native mouse, key, and committed-text event.
- AC-5: The demo visibly contains VBox, text, image, editable text field,
  button, scroll region, embedded Simple 2D, embedded Simple Web, and status.
- AC-6: Button click, typing and Ctrl shortcuts, 2D drag, titlebar drag,
  scrolling, minimize/restore, exact maximize/restore, pin/unpin, and close
  advance semantic state and render revisions.
- AC-7: Pin/unpin operates on stable `app_id` values and persists; closing the
  last window removes only the running taskbar item.
- AC-8: Button activation advances a deterministic non-silent mixed-PCM frame
  count; device backends remain separate from the mixer.
- AC-9: Closing all windows returns window, event, content, pixel, and audio
  handle counts to their measured baseline and cancels pointer capture.
- AC-10: Isolated native regressions cover trait dispatch, aggregate by-value
  calls/globals/returns, Option/Result aggregate payloads, arrays in returned
  structs, nested returns, entry closure, and strong/weak symbol selection.
- AC-11: SDL3, SDL2, QEMU HDA DMA/IRQ, and QRB2210 SimpleOS rows reuse the same
  contracts and stay failing or unsupported until runtime evidence exists.
- AC-12: Executable runtime evidence plus current generated manuals is the
  release gate; source inspection and scenario prose are not proof.

## Scope Exclusions
- macOS-style visual polish, animation, accessibility, browser-engine expansion,
  GPU acceleration, and multi-monitor behavior.
- Treating the STM32U585 MCU port as an UNO Q desktop result.
- Claiming SDL, QEMU, HDA, or QRB2210 completion from host/headless evidence.

## Cooperative Review
- Prior research sidecars: `wm_local_research`, `sound_local_research`,
  `compiler_research`, `domain_research`, and `docs_research`.
- Merge owner and final high-capability reviewer: root Codex lane.
- Read-only implementation sidecars: `skia_dedent_root`,
  `wm_minimal_live_closure`, and `wm_lifecycle_leak_next`; root Codex owns
  edits, merge, and final review.

## Frozen Shared Names
- Event record: `WindowEventRecord`
- Event queue: `WindowEventLoop`
- Window facade: `SimpleWindow`
- Content interchange: `WmContentFrame`
- Content origins: `gui`, `simple_web`, `pixel_surface`
- System scenario helper: `step("...")`
- Evidence helpers: `capture_wm_state`, `capture_frame`, `capture_pcm`
- Fail-fast placeholder: `expect(false).to_be(true)`

## Phase
implementation-in-progress

## Log
- dev: Refined the broad request into 12 fail-closed acceptance criteria.
- research: Saved local/domain research, selected requirements, architecture,
  detail design, GUI design, system-test plan, and agent task plan.
- spec: Added normalized event/window unit specs and a red host content-frame
  admission truth test.
- impl: Added scalar normalized events, bounded event/text storage, explicit
  capabilities, deterministic headless window handles, and pixel-frame origin.
- compiler: Extended the isolated native aggregate/trait regression fixture.
- impl: Generalized host frame admission to validated GUI/Web/pixel origins and
  added nested child-frame ownership.
- impl: Replaced SimpleOS `WindowSurface.session: any` with explicit content
  kind plus scalar generation handle; GUI and Web now dispatch to their own
  WmContentFrame producers.
- impl: Added RenderSurface coordinate translation, stable app_id pin/unpin
  persistence, explicit unsupported headless operations, and close-time content
  count cleanup.
- audio: Replaced raw miniaudio pointers with synchronized generation handles,
  idempotent teardown, natural-completion reaping, and live-handle counters.
- glfw: Added a dynamically loaded Linux GLFW runtime, normalized callback
  queue, retained presentation path, explicit unavailable statuses, Simple
  facade, C self-check, and Linux-host native-runtime compilation wiring.
- compiler: The expanded native regression reaches a real compiler failure
  (`fld_base_sym not found`); the full Simple closure is separately blocked by
  the pre-existing Skia shaper dedent error. Both are recorded without retry.
- evidence: Added the RED runtime-evidence manual; no source-only pass is
  accepted.
- impl: Added the live GLFW demo entry, one authoritative host event router,
  desktop-to-client coordinate translation, separate committed text, button
  action consumption, and event-driven GUI/Web/2D frame regeneration.
- audio: Added deterministic 48-kHz stereo UI-click PCM, a direct owned-PCM
  miniaudio path, live playback cleanup, and a C runtime check that starts PCM
  playback and returns handles to baseline.
- audio-hardening: `SoundEngine` now retains the device handle instead of
  reinitializing during teardown, and UI-click synthesis owns one local PCM
  buffer instead of crossing aggregate-return boundaries. An isolated Phase 3
  native probe still exits through an impossible `play_ui_click` success
  branch with `device_started=false`. A smaller class-receiver plus local-buffer
  compiler control passes, so the remaining failure is inside the larger
  SoundEngine method/return lowering rather than every receiver read. The
  failing sound probe and passing compiler control are retained; the
  three-cycle sound cap was reached.
- gate: Self-hosted production evidence, real GLFW presentation, WM client
  routing, and mixed PCM remain open; no release claim is permitted yet.
- native: Per user direction, stopped the Rust-seed entry build and used
  `build/aggfix/stage3/simple` directly with a preserved native cache. Two
  old-parser line-break incompatibilities in `host_compositor_core.spl` were
  normalized; the third bounded attempt reached the pre-existing Skia shaper
  dedent blocker. No bootstrap or Phase 2 retry was run.
- wm: Added the canonical scalar Normal/Minimized/Maximized/Closing/Closed
  transition owner and wired SimpleOS minimize/restore/focus/capture lifecycle
  through it. The aggregate-fix Phase 3 compiler built and ran the direct
  lifecycle probe (`WM WINDOW STATE PROBE: PASS`); the full compositor T0 check
  remained diagnostic-only and timed out in the pre-existing compiler closure.
- wm-events: Extended the SimpleOS generation-handled GUI registry with
  retained focused-widget state, removed the `update_tree` mutation that
  immediately converted GUI content back to Web, and routed client-local
  pointer events through a locally reconstructed session. Scalar GUI capture
  survives out-of-bounds movement until release and is canceled by
  minimize/close; no large session aggregate is stored in the compositor.
  Added focused physical-key and separate committed-text dispatch plus a
  scalar desktop clipboard seam for Ctrl+A/C/X/V across reconstructed
  sessions. The shared InputBackend path now feeds printable key/text events
  instead of fabricating Ctrl+Alt shell shortcuts.
- event-native: Replaced `[WindowEventRecord]` queue storage with a packed
  sixteen-word scalar ring and a status-based `poll_scalar()` boundary. The
  isolated Phase 3 native FIFO/text/overflow/generation probe passes.
- qemu-input: The raw PS/2 route now retains modifier state, decodes the MVP
  Set-1 printable/special-key subset, routes focused GUI key then committed
  text, and owns Alt+Tab/F4 plus Ctrl+M/Ctrl+Shift+M. Its isolated Phase 3
  decoder probe passes with no `char_from_code` weak stub.
- host-events: The GLFW demo now drains the normalized queue only through
  `poll_scalar()` and routes scalar fields into `HostGuiEventRouter`. GLFW
  callback ingestion now also writes the flat scalar ring directly; aggregate
  event construction remains compatibility-only. The expanded Phase 3 scalar
  enqueue/poll probe passes. A canonical capture/text routing spec was added
  but cannot execute until Skia discovery is repaired.
- taskbar-pin: SimpleOS now keeps an ordered stable-app-id pin authority,
  handles idempotent pin/unpin runtime commands, launches through the retained
  display name, keeps running-window entries after unpin, and fail-closed
  loads/saves `/SYS/TASKBAR.PIN` through the shared VFS. The bounded wire
  codec builds and runs with the aggregate-fix Phase 3 compiler; live reboot
  persistence remains a runtime gate.
- host-taskbar-pin: The GLFW demo now seeds `HostCompositor` from the persisted
  stable-`app_id` runtime through scalar accessors. Successful Ctrl+P changes
  both persistence and the rendered canonical `TaskbarModel`; failed saves no
  longer fabricate a visible state change. Native-pixel taskbar hit testing
  now follows the same pinned-then-running 56-pixel slots as the rendered
  shared taskbar and restores/focuses an existing window through its pinned
  app slot. An idle pinned slot now emits a one-shot stable `app_id` only on
  release-inside; drag-away cancels it. The live GLFW demo keeps the desktop
  alive after internal close, consumes that id, and recreates the same app;
  live closure evidence remains blocked by Skia discovery.
  The focused Phase 3 compositor probe is present, but its entry closure
  reaches the unchanged Skia shaper dedent during discovery, so this row
  remains runtime-blocked.
- wm-pixels: Implemented the previously dead `PIXEL_SURFACE` content kind with
  generation handles, a bounded raw-memory registry behind one scalar address,
  revision updates, close-time release, scalar SimpleOS backend writes, and
  `WmContentFrame` emission in the high-level shell. Phase 3 probes reproduce
  aggregate-held array corruption and pass the replacement raw store. The
  store now blits directly into bounded pitched ARGB32 scanout memory through
  the exact-width pure `simple-core` store; its Phase 3 archive-linked probe
  passes without an aggregate or trait boundary. Full compositor execution
  remains behind the Skia discovery blocker, and scalar trait dispatch is
  still a separate runtime gate.
- audio-raw: Added an array-free deterministic stereo click generator and a
  scalar raw-PCM miniaudio entry. The generator/checksum passes an isolated
  Phase 3 native probe, the C backend passes fail-closed coverage, and a real
  host miniaudio smoke opened a device, created a playback handle, observed
  one live voice, then returned to zero with idempotent stop/shutdown. The
  demo uses this path.
- host-glfw: The dynamically loaded GLFW/OpenGL backend now has real live
  evidence under Xvfb: two non-black ARGB presentations, native X11 key,
  committed-text, pointer-motion and button events, clipboard round-trip,
  generation-safe idempotent teardown, and a zero live-window count. Each
  window retains one OpenGL texture and one grow-only CPU staging buffer; the
  two-frame probe proves exactly one buffer growth. The live path now accepts
  the authoritative raw framebuffer address/count directly, and the full demo
  uses that scalar ABI instead of rebuilding/passing `[u32]`. This is the
  runtime boundary probe, not yet the full WM scene.
- wm-capture: Host GUI pointer-button events now consume their own normalized
  coordinates, and captured drags continue with current client-local
  coordinates after leaving the client bounds. A missing/minimized capture
  owner cancels capture instead of replaying stale coordinates. The focused
  Phase 3 probe remains blocked by the known Skia discovery dedent; the Phase 2
  compiler additionally cannot parse the current scalar window-event module.
  Three bounded compiler attempts were exhausted without bootstrap.
- audio-demo: The GLFW demo remains on the verified scalar raw-PCM click path;
  the aggregate `SoundEngine.play_ui_click()` receiver stays RED in Phase 3 and
  is not promoted into the live demo.
- wm-shortcuts: Added one scalar normalized shortcut classifier and made the
  GLFW demo consume Alt+Tab, Alt+F4, Ctrl+M, and Ctrl+Shift+M before GUI
  routing; Ctrl+C and key releases remain client events. The isolated Phase 3
  archive-linked probe passes through the pure `simple-core` runtime without a
  full bootstrap.
- wm-close-baseline: The GLFW demo now requires external-frame IDs, parent and
  child frames, native content-cache IDs/objects, host windows, queued events,
  text-arena entries, and audio playback handles all to return to baseline
  after close. The shared scenario asserts the compositor-owned subset.
- wm-restore-state: Host restore now matches the canonical state machine:
  restoring a minimized maximized window first returns to its maximized
  geometry, and only the next restore returns to the exact saved normal
  rectangle. Maximize now ends above the 56-pixel taskbar instead of
  overlapping it by eight pixels, and restore clears stale focus on sibling
  windows. The isolated Phase 3 lifecycle probe is present but discovery still
  stops at the unchanged Skia shaper dedent; no bootstrap was attempted.
- wm-interaction-cancel: Host minimize, maximize, and close now share one
  target-scoped cancellation path for chrome drag, resize, and armed
  release-inside actions. Minimize cancels only after the target is actually
  minimized, so an unauthorized request cannot disrupt an active interaction.
- wm-focus-cycle: Host Alt+Tab focus cycling now matches SimpleOS by skipping
  minimized windows instead of implicitly restoring them. It wraps across
  visible z-order and leaves an all-minimized desktop unfocused.
- wm-resize-capture: The shared pointer reducer now mutates geometry only while
  `resizing` is captured; resize-grip hover is recomputed on every move and
  moving away before press clears the candidate. Normalized button events also
  update compositor coordinates before chrome hit testing, so a button event
  never reuses stale pointer state.
- wm-missed-release: A new normalized left press cancels stale client and WM
  drag/resize capture before applying its coordinates, then recomputes the
  current hover target. A missed prior release can no longer move or resize an
  old window before the new press is routed.
- wm-taskbar-geometry: Host Draw IR, direct pixel rendering, pinned/running hit
  testing, tray reservation, and launcher release checks now share 56-pixel
  taskbar slots. The prior 44/56 split could draw a second launcher at a
  different location from its clickable region.
- wm-taskbar-active: Draw IR, backend, and raw pixel taskbar executors now
  resolve each running `window_id` against the authoritative scene: minimized,
  focused, and inactive windows receive distinct theme colors. `WindowRef`
  stays unchanged, avoiding a parallel focus authority.
- host-pointer-buttons: The normalized host router now records left, middle,
  and right button state in the compositor. Only left reaches the current
  widget reducer because that reducer does not yet distinguish button values;
  the focused spec proves right-click creates no false primary-click event.
- hda-pci-runtime: The authoritative x86 bundle already owned scalar PCI
  enumeration/field/BAR providers; memory+bus-master enable was the only
  missing HDA extern and is now real. Flagged MMIO BAR0 values are normalized,
  and raw-pointer providers now back the DMA resource table. A pure-Simple
  config-port replacement still exits 139 under Phase 3 and remains tracked as
  an optional boundary migration, not a QEMU HDA blocker.
- hda-stream-irq: The x86 desktop now starts a scalar-owned HDA service that
  prepares a four-period silent BDL/PCM ring, selects the GCAP output stream,
  enables its INTCTL bit, installs a level/active-low Q35 I/O-APIC route and IRQ
  handler before RUN, assigns stream tag 1, consumes the hardware RIRB response
  slot, and requires four IOC completions in the canonical QEMU WM gate.
  Controller/RIRB and I/O-APIC sequencing pass isolated Phase-3 native probes.
  The expanded DMA probe remains RED on the Phase-3 EOF/dedent parser defect after the
  mandatory three-cycle cap; no bootstrap or live QEMU run was attempted.
- uno-q-target: A Phase-3-green scalar contract now makes QRB2210 the only UNO
  Q desktop target and returns explicit `port-unavailable` for display,
  normalized window events, and audio until its AArch64 port exists.
  STM32U585 returns `unsupported-mcu` and cannot satisfy a WM claim. The new
  fail-closed checker exits 1 with `qrb2210-simpleos-port-unavailable`; no board
  was connected over ADB.
- host-sdl2-boundary: The SDL2 runtime now skips unsupported native events
  while preserving later supported events, exposes retained committed UTF-8
  text, and provides real wait, size-limit, minimize/maximize/restore,
  decoration, always-on-top, focus, flags, fullscreen-status, and error calls.
  The Simple wrapper reports an actual zero/one snapshot count instead of the
  requested maximum, maps window subevents, and no longer fabricates the
  corresponding state queries. A dummy-video native probe passes with ignored
  event + text + Ctrl+A ordering and real window operations. The Phase-3
  archive completed on its third bounded attempt with the older compiler's
  known re-export warnings; a file-scoped production check hit the existing
  60-second CLI-driver timeout and was stopped without bootstrap or retry.
- host-sdl2-audio: SoundEngine can now select an SDL2 queued device without
  changing its deterministic click PCM producer. The boundary uses a positive
  generation handle, rejects stale handles and format mismatches, clamps
  `f64` to exact 48-kHz stereo `f32`, records submitted frames, closes
  safely, and reports underrun counting as unsupported (`-1`). Duplicate close
  is a safe no-op reported as false rather than fabricated success, and PCM
  lengths beyond SDL's `Uint32` queue boundary are rejected before allocation.
  The live dummy-audio probe passes with strict C warnings enabled. The current
  native compiler still requires the host runtime object to be supplied
  explicitly; demand-selected host provider compilation remains an open
  compiler lane.
- audio-handle-truth: SoundEngine cleanup no longer returns a fabricated zero
  after clearing `device_started`. Each miniaudio client now owns a distinct
  generation-counted engine handle; closing one client preserves the shared
  device and playback for remaining clients, and only the last close releases
  global resources. Duplicate stale close is a safe no-op reported as false.
  The full-stack demo records the real pre-start device/source/playback
  baseline and requires the same count after teardown. The strict native
  two-client raw PCM probe passes init, first-client close, continued playback,
  stop, stale-close rejection, final close, and zero live-handle checks.
- host-resize-rendering: The GLFW facade now exposes logical window size
  separately from framebuffer size and content scale. The live demo renders
  and presents at current framebuffer dimensions, scales logical pointer
  coordinates into that pixel space, and consumes normalized framebuffer
  resize events. Maximized internal windows reflow to the new work area while
  retaining their exact saved normal rectangle. Oversized framebuffer requests
  fail closed before pixel-count overflow/allocation. The GLFW C boundary
  compiles cleanly with strict warnings; live Xvfb execution remains
  unavailable on this host because no `libglfw.so` is installed.
- render-surface-event-route: Embedded 2D dragging now consumes only a
  normalized left-button press that the authoritative client router accepted.
  Titlebar/right-button presses cannot reuse stale client coordinates, a new
  left press cancels missed-release drag state, and left release terminates
  capture even outside the panel. Consumed WM/application shortcuts also
  clear client and embedded-surface capture. The focused system spec exercises
  a real client-to-titlebar transition and captured move/release; execution
  remains pending behind the already-recorded pure-Simple source-closure gate.
  Consumed shortcuts force a new frame without overwriting pin/unpin status
  with the generic `Key event` label.
- phase3-skia-discovery: The original `ot_layout_shaper.spl` conditional
  dedent was normalized for the older Phase-3 grammar. An isolated shaper
  entry then advanced to `ot_layout_gpos_data.spl`, where the same parser
  still reports a function-end dedent after the mandatory three bounded
  attempts. The full WM closure was not retried and no bootstrap was run.
- qemu-external-runtime: The canonical QEMU gate ran without a kernel build,
  using the validated external ELF
  `f783a111a63ea781e447d6396cc33bf8be9f0723675479bec13a85ed9a33e4c9`.
  Serial evidence reached GRUB, `[BOOT64] call _start`, BGA 1024x768x32
  programming, PS/2 mouse initialization, and the legacy glass desktop.
  The run correctly failed `dynamic-scanout-or-desktop-readiness-missing`:
  the old artifact emitted no dynamic scanout/readiness, content provenance,
  correlated input/frame, or HDA init/IRQ markers. This is a real QEMU
  boot/display baseline, not evidence for the current source or HDA service.
- wm-dynamic-window-id: The live demo now retains the compositor-generated
  window ID and replaces it after pinned-taskbar reopen. GUI/child frames,
  event routing, lifecycle shortcuts, and cleanup all target that live ID
  instead of stale window `1`. The scenario asserts a newer reopened ID and
  maximize/restore through it; live execution remains behind the recorded
  renderer discovery blocker.
- simpleos-action-truth: The shared SimpleOS action applier now rejects every
  non-create action for a nonexistent surface before owner lookup or no-op
  dispatch. The focused unit scenario covers destroy, focus, resize, move,
  title, minimize, maximize, restore, and tree update. The Phase 3 compiler has
  no test command, so these authored assertions remain pending a test runner.
- sdl2-web-primary-click: The SDL2 Web input bridge now consumes the runtime's
  normalized `0=left` value, arms click state only for a primary-button down,
  and cannot turn a right-button press into a later left click. Its isolated
  production-helper Phase 3 entry probe builds and runs
  (`WEB UI PRIMARY BUTTON PROBE: PASS`).
- taskbar-running-pin-activation: Shared taskbar dispatch now treats scene
  z-order as the most-recent-window authority for a stable `app_id`. A pinned
  running app focuses that window, restores it in the SimpleOS live shell when
  hidden, and clears stale minimized runtime evidence; launch is emitted only
  when no matching window exists. The isolated production-path Phase 3 probe
  builds and runs (`SHARED WM PINNED RESTORE PROBE: PASS`).
- taskbar-fresh-demo-pin: A fresh host demo layout persists the stable demo
  launcher before mirroring it into the compositor and before opening audio.
  Failure exits without acquired PCM/device resources; closing the last window
  therefore retains the launcher path needed to recreate a newer window ID.
- host-focus-capture: Host GUI pointer capture is canceled when its internal
  window loses focus. A later release, even over the old client bounds, is not
  delivered as a matching client release. The focused router assertion is
  authored; its full test closure remains behind the recorded renderer
  discovery blocker.
- phase3-gpos-discovery: Parenthesized the GPOS variation-store multiline
  condition rejected by the older Phase-3 parser. The focused pure-Simple
  source-entry closure now builds 11 modules and links successfully without a
  bootstrap; the capped full WM closure was not rerun.
- wm-close-minimized-cleanup: Closing a minimized window now removes its stale
  minimized runtime evidence while recording the close. The dedicated
  pure-Simple Phase-3 probe builds and runs
  (`WM CLOSE MINIMIZED CLEANUP PROBE: PASS`).
- phase3-full-closure: Parenthesized the two remaining multiline Web
  conditions rejected by the older Phase-3 parser. The full demo entry closure
  now builds with `build/aggfix/stage3/simple`: 512 modules on the cold pass,
  then 509 cached modules after the theme changes. No bootstrap was run.
- phase3-host-providers: Reused `SIMPLE_LINK_OBJECTS` to link the existing GLFW
  and miniaudio C providers. Active `rt_glfw_*` and `rt_audio_*` symbols are
  real definitions in the executable; preload is no longer required. Native
  execution passed host and audio initialization plus theme loading after
  replacing two known erased-result `.to_i32()` misdispatches with typed
  scalar casts. The third capped live attempt now faults in
  `ProfileResolver.orientation_changed()` from `UISession.dispatch()`, before
  a capturable WM frame.
- ui-resize-native: `UISession.dispatch(UIEvent.Resize)` now commits the event
  dimensions to the session viewport before recomputing its profile, and the
  read-only profile comparison uses the established native-safe receiver form.
  The focused Phase-3 probe reproduced the exact
  `ProfileResolver.orientation_changed()` segfault before the change, then
  passed with a 40x60 Portrait viewport afterward.
- phase3-gui-render-entry: The next full linked host run passed the repaired
  resize/profile route and reached
  `widget_tree_to_draw_ir_with_theme()`. It now fails closed in
  `common.ui.widget_draw_ir._emit_widget()` before the first capturable frame.
- widget-draw-ir-native-safe: Disassembly proved `find_rect() ->
  WidgetRect?` returned a raw aggregate that native Option unwrapping converted
  to tagged nil. Layout now exposes a scalar `find_rect_index()`, and the
  canonical widget Draw-IR main/scroll paths read the matching array element
  directly; scroll batch construction no longer returns an aggregate Option.
  The exact demo-tree probe moved past `_emit_widget()` into font loading.
- phase3-font-provider-chain: Targeted no-mangle pure-Simple
  `core_sha256.spl` and `core_fs.spl` archives now supply
  `rt_file_hash_sha256` and `fs_copy_cstr` without a bootstrap or C shim. The
  exact demo-tree widget Draw-IR probe passes with root, button, scrollbar,
  embedded 2D, and embedded Web commands.
- phase3-initial-gui-frame: The first GUI frame now uses scene revision
  `render_revision + 1`; revision zero is intentionally rejected by the
  fail-closed GUI frame producer.
- host-router-native-safe: The focused native pointer-routing probe exposed a
  corrupted nested compositor receiver after the aggregate target result was
  removed. The live GUI router now performs its small scalar client hit-test
  inline; its Phase-3 pointer-capture probe exits cleanly.
- phase3-widget-mutation-dispatch: Disassembly proved each chained
  `tree.find_widget(...).set_prop(...)` compiled as
  `WidgetStore.set_prop()` on the aggregate `WidgetNode?` result. The demo now
  uses direct stable-ID `WidgetNode` handles. The exact demo-tree probe passes
  native mutation, property readback, and canonical Draw-IR generation, and
  the rebuilt `spl_main` calls only `WidgetNode.set_prop()`.
- host-glfw-packed-argb: The raw presenter now consumes the compositor's
  packed four-byte ARGB32 buffer instead of reading eight-byte words past its
  allocation. The live C probe deliberately uses a valid four-byte-aligned,
  non-eight-byte-aligned buffer and passes two-color presentation, two frame
  sequences, native key/text/pointer/button input, and clean teardown
  (`colors=2`, `mean=0.366013`, SHA-256
  `ee82698fd31521729756cd3f7dcf6fe3a4c3dcc73290deb87aa431871463addb`).
- host-glfw-title-abi: `SimpleGlfw.create_window()` now reuses the established
  scalar `spl_str_ptr()` bridge rather than passing a runtime `text` header as
  `const char*`. The rebuilt full demo is discoverable by its exact
  `Simple Full Stack WM Demo` title.
- runtime-boundary-decision: `runtime_need=GLFW owns the final native window
  and packed-pixel copy`; `facade_checked=SimpleGlfw is the existing owner`;
  `chosen_path=reuse-facade plus existing spl_str_ptr bridge`;
  `rejected_shortcuts=no app-side pixel repack, no C title copy, no second
  presenter`.
- host-mapped-frame: The exact-title 640x600 full-demo window still captures
  as a one-color black image (mean/min/max zero, SHA-256
  `0b56d6bd870958ec99fb98026aa09e576e046046c5815efe02d39c9f8d393cc1`).
  A bounded live run then faults in `rt_to_string()` before the post-input
  capture. The next host gate is compositor pixel population/native string
  conversion; the corrected GLFW raw copier itself is independently green.
- host-native-id-render-boundary: Operational WM numeric IDs now use the
  existing raw-i64 text formatter instead of the generic tagged
  `rt_to_string()` path in the demo, content admission, MDI scene projection,
  child cleanup, taskbar projection, and Web fallback. External GUI/pixel
  frames also no longer load/hash the Simple Web theme merely to calculate an
  unused fallback revision. The focused Phase-3 first-frame probe advanced
  from two reproducible `rt_to_string()` faults to exact nonzero pixel
  `0xff112233`; its second assertion exposed a row/column test-pattern mistake,
  which is corrected but intentionally not rerun after the three-cycle cap.
- host-live-after-id-boundary: The rebuilt full demo still creates the exact
  titled X11 window but faults before a two-second capture. No live non-black
  or semantic-input claim is made. The focused compositor result narrows the
  remaining defect to the richer GUI/demo path rather than raw framebuffer
  allocation, external-frame admission, base compositor paint, or GLFW's
  packed-pixel copier.
- ui-native-scalar-text-owner: The generic tagged `rt_to_string()` route
  faults on typed `i32`/`i64` values in the Phase-3 native UI path. One
  `common.ui.native_scalar_text` owner now wraps the runtime's existing raw-i64
  formatter. Builder dimensions, RenderSurface handles, UISession identities,
  selected event receipts, and WM numeric IDs reuse that owner; the direct
  demo/compositor/MDI `rt_*` declarations from the prior checkpoint are
  removed.
- ui-native-scalar-runtime-decision: `runtime_need=project typed UI/WM scalar
  identities without the corrupt tagged formatter`; `facade_checked=no
  existing common UI scalar-text owner; the runtime already exposes the exact
  raw-i64 primitive and the stale Phase-3 compiler cannot be refreshed without
  the prohibited bootstrap`; `chosen_path=add-smallest-owner-facade`;
  `rejected_shortcuts=no app-side raw externs, no per-widget decimal
  implementation, no full bootstrap, no feature-only bypass`.
- phase3-gui-first-frame-probe: The existing native first-frame probe now uses
  the exact full-stack demo tree, `UISession`, canonical GUI content-frame
  producer, external-frame admission, and raw compositor readback. Three
  bounded cycles moved its first fault from `builder.with_height()` to
  `_ui_draw_ir_session_nonce()`, then `UISession.dispatch()` receipt
  formatting, and finally `common.ui.event.process_event()` viewport token
  formatting at `event.spl:66-67`. The final binary still exits 139; no full
  live retry was run behind a red focused gate.
- phase3-gui-event-theme-progression: Three further focused cycles moved the
  exact GUI producer probe past canonical Resize token storage, theme source
  manifest path-length formatting, and text-only CSS splitter interpolation.
  Every build reused the warm Phase-3 cache; the last compiled 3 modules and
  reused 377. The remaining first `rt_to_string()` caller is
  `common.ui.theme_render_snapshot.normalized_theme_material_text()`, whose
  material checksum serialization still interpolates scalar aggregate fields.
  The final probe exits 139, so no GLFW retry or pixel claim follows.
- native-event-sibling-audit: Pointer/scroll diagnostic payloads in
  `UISession.dispatch()` and scroll/caret property writes in
  `common.ui.widget_hit` still contain generic numeric interpolation. They
  remain active event-hardening work, but were not changed speculatively before
  the first-frame producer gate reaches them.
- phase3-theme-material-to-pixel-boundary: Theme material checksum
  serialization now uses direct text concatenation and the common native scalar
  owner for every numeric field, with explicit lowercase booleans. The exact
  GUI producer probe advances past theme loading without a fault. Its width and
  height are correct, but the returned pixel array length is invalid (exit
  `33`). A third-cycle experiment reading pixels directly from `Engine2D`
  produced the same result and was reverted as ineffective. The remaining
  focused blocker is the native aggregate/trait pixel-return boundary in the
  Draw IR renderer, not GLFW presentation; no live retry was run.
- phase3-exact-image-fixture-correction: The preceding pixel-boundary
  diagnosis is superseded. The demo tree always emits
  `wm-demo://image`, while the probe passed an empty resolved-image list.
  Draw IR correctly counted the missing image as skipped, and the GUI adapter
  correctly returned an empty fail-closed frame. The probe now supplies the
  exact production 2x2 image. Its cached Phase-3 build compiled 2 modules,
  reused 378, and exits `0`, proving canonical GUI frame dimensions, 6000
  pixels, checksum, external-frame admission, and raw compositor pixel
  `0xff0e0e10`. No pixel aggregate failure remains proven at this boundary.
- host-glfw-live-nonblack: GDB identified the next live fault as generic
  interpolation inside `ui.web.html_css.responsive_css()` while constructing
  the default pinned-app manifest. That shared CSS owner now uses direct text
  concatenation and `ui_native_i64_text()` for breakpoint values. The fresh
  build compiled 3 modules and reused 511. Xvfb `:77` then captured the exact
  titled 640x600 GLFW window with 138 colors and SHA-256
  `43ef5a5e3047c2064b5419c3ae9ec837995dd36a8de3a229ad72b6c0214c45c8`
  at `/tmp/wm_full_stack_demo_v4.png`. The window is non-black and visibly
  contains WM chrome/content/taskbar, but widget layout is collapsed and
  overlapping. Native `windowclose` removes the X11 window but does not stop
  the demo loop; it required Ctrl-C. No clean-close or complete widget-layout
  claim is made.
- phase3-vbox-layout-regression: Two small-model audits traced the visible
  overlap to `WidgetRect[]` transport, not VBox arithmetic. The exact demo has
  fixed row Y coordinates (`button=90`, `status=374`) and stable IDs. The
  extended native first-frame probe finds both IDs but exits `23` because the
  returned button Y is corrupt. Three bounded cycles showed that moving field
  reads behind accessors and snapshotting the already-returned array cannot
  recover the geometry; that ineffective implementation was removed. The
  retained red regression proves the next repair must write scalar geometry
  during layout traversal, before any aggregate-array return boundary.
- host-glfw-close-flag-consumer: The demo now consumes the existing
  `SimpleGlfw.should_close(host_window)` signal after draining normalized
  events. The cached full build compiled 2 modules and reused 512. Xvfb `:77`
  has no window manager, so `xdotool windowclose` destroys the X11 surface
  without setting GLFW's close flag or producing a valid callback request; the
  process remained alive and was stopped with Ctrl-C. This environment cannot
  certify outer close, but real-host close flags will no longer be ignored.
- phase3-vbox-in-traversal-scalar-experiment: Two small-model reviews confirmed
  that recursive layout order and the returned ID-array order are both
  preorder. A raw scalar geometry mirror was therefore written at
  `_compute_layout()` entry before recursion. The first cached native build
  compiled 4 modules, reused 376, and still exited `23`. A diagnostic build
  compiled 2/reused 378 and encoded the stored button Y as `1`. Replacing the
  i32 store/readback with an i64 store/readback compiled 3/reused 377 and still
  exited `23`. The experiment was reverted: the corruption exists before or
  during the scalar push call, not only in the returned `WidgetRect[]`.
  Per the three-cycle cap, no live rebuild was attempted.
- phase3-vbox-cursor-and-compiler-isolation: The exact root is a bordered Panel,
  so the correct button/status Y oracle is `91/375`, not `90/374`; the retained
  probe was corrected. The observed button Y of `1` is the panel inner origin,
  proving `cur_y` does not survive the call-bearing child loop. A fresh
  pure-Simple Stage-2 build of the probe still exited `23`, and changing only
  the two VBox loops from `for` to indexed `while` also exited `23`; that
  ineffective source workaround was reverted. A cache-preserving, no-stub
  compiler refresh from the existing Stage-2 binary was attempted without a
  bootstrap. It failed closed on `GlobalFlags.mem_infra_requested`,
  `SdnValue.empty`, and `ANY.is_empty` HIR/MIR lowering errors before producing
  a compiler executable. No live demo rebuild was justified.
- phase3-compiler-refresh-source-unblock: Parallel small-model audits showed
  all three compiler-entry failures were real source defects. `GlobalFlags`
  now declares and parses the already-consumed `--mem-infra` and
  `--mem-infra-strict` values; the SDN no-op backend emits the direct scalar
  `SdnValue.Null` variant; and coverage threshold parsing uses the typed empty
  text comparison instead of invalid `.is_empty` field syntax. The first
  cached rebuild cleared two failures and exposed Stage-2 enum static-helper
  resolution, fixed by the direct variant. The next two builds compiled the
  full closure and reached link. Both failed because the Stage-2 native-build
  driver still selected the intentionally minimal `core-c-bootstrap` lane,
  leaving compiler/host runtime symbols such as `rt_index_of`,
  `rt_cranelift_*`, and `rt_file_stat` unresolved. The source fixes are kept;
  no compiler executable or WM rerun is claimed.
- phase3-focused-runtime-capsule-build: The next audit corrected the compiler
  recipe: build the single positional `src/app/cli/bootstrap_main.spl` entry
  from admitted Stage-2 and supply the authoritative Stage-2 runtime path, so
  runtime projection plus compiler backfill—not direct `native_all`
  injection—owns `rt_index_of`, `rt_cranelift_*`, and `rt_file_stat`. That
  focused build ran for 10m42s at ~100% CPU but produced zero cached objects.
  A concurrent identical canonical build in the shared workspace was already
  7h45m old at ~99% CPU. This matches the documented pre-object runaway
  signature, so the scoped process was terminated with exit `130`; its empty
  cache was preserved. No full bootstrap, Rust-seed fallback, or WM claim was
  made.
- phase3-vbox-raw-cursor-stack-experiment: A bounded raw i64 cursor stack was
  tested as the smallest layout-local workaround. It advanced each VBox slot
  before recursion, used a separate depth for the nested scroll VBox, and
  packed child Y/height into one raw record to avoid aggregate transport.
  Cycle 1 compiled 8/reused 372 and still exited `23`. Cycle 2 compiled
  3/reused 377 and exited `28`, proving the root raw slot did not reach the
  final status Y `375`. Cycle 3 compiled 2/reused 378 and again exited `28`;
  the raw value matched none of the expected row origins
  `1/25/61/91/123/195/285/375`. The ineffective production stack and probe
  hooks were reverted. The exact regression keeps the corrected panel-inner
  button width `478` instead of `480`.
- host-glfw-single-pump-event-drain: Parallel event audits found that the
  canonical GLFW facade re-entered `glfwPollEvents()` before every FIFO pop,
  allowing sustained input to starve rendering. The runtime now exposes one
  native pump plus FIFO-only pop operations; the facade pumps once and drains
  the finite queued snapshot. The no-display C selfcheck exits `0`. The Xvfb
  live probe passes real key, committed text, pointer motion, and button input.
  The full Simple WM demo closure linked with the new runtime object
  (`3 compiled / 511 cached`); no new rendering claim is made.
- simpleos-remote-committed-text: Remote SimpleOS windows previously received
  pointer events only; PS/2 text was consumed by local GUI sessions before the
  WM IPC boundary. `WmEventType.Text` now remains separate from physical keys,
  the existing event wire appends bounded UTF-8 without renumbering older
  event kinds, and the client rejects malformed/truncated payloads. The QEMU
  path carries scalar scancode/modifier state through the freestanding
  compositor boundary and reconstructs ordered key-then-text events in the
  shell before delivery. PS/2 polling returns after one routable key so the
  hardware FIFO, rather than an overwriteable aggregate queue, preserves
  bursts. Remote content polling is re-armed after keyboard input.
  A pure-Simple Stage-2 native probe linked and exited `0`. An attempted
  aggregate-returning modifier decoder crashed with a nil receiver, so it was
  deleted in favor of scalar inline packing/unpacking.
- wm-taskbar-persistence-transaction: SimpleOS pin/unpin previously mutated
  ordered app-id state and returned success even when VFS persistence failed.
  Both paths now roll back and return false. The focused spec also covers
  persisted unpin and running-item removal after close. A pure-Simple Stage-2
  probe compiled only with unresolved stubs and faulted in cross-module
  `g_mount_table` access; that run is rejected as evidence and leaves the live
  persistence gate red. The no-stub rebuild fails closed on unresolved VFS,
  logging, FAT32, and panic owners.
- wm-taskbar-secondary-action: Secondary-clicking a pinned taskbar slot now
  emits `unpin_app`; secondary-clicking a running slot emits `pin_app`. Both
  carry the authoritative scalar `app_id` through the shared runtime command
  adapter to host and SimpleOS persistence owners. The browser taskbar now
  forwards its native `contextmenu` event into that same boundary; SimpleOS
  already normalizes button code 3 to `right`. Secondary clicks outside the
  taskbar remain ignored. A no-stub pure-Simple Stage-2 native probe
  linked with zero unresolved stubs and exited `0`. The wider host `WmBridge`
  closure compiled but did not link because the selected core runtime capsule
  intentionally excludes SQLite, so live host persistence remains a runtime
  gate rather than inferred evidence.
- wm-content-kind-render-gate: Current source no longer routes every body
  through Simple Web. SimpleOS baremetal emits GUI, Web, and pixel
  `WmContentFrame` values through the shared Engine2D executor; the legacy
  `Compositor.render_all()` compatibility path also has three explicit
  branches. A focused headless probe now checks all three rendered bodies and
  post-close handle baselines. Its no-stub Stage-2 closure compiles but the
  admitted core capsule lacks required Web/GPU/SQLite symbols; `simple-core`
  is absent and the bounded Cranelift attempt produced no artifact. Runtime
  evidence remains red.
- wm-host-content-owner: Host BrowserRenderer eligibility no longer derives
  from `owner_port`. A scalar content owner is created explicitly, preserved
  across lifecycle mutations, changed only after validated GUI/pixel frame
  admission, and restored when the frame is released. This prevents hosted
  Web frames from overwriting admitted GUI/pixel content. A no-stub
  pure-Simple Stage-2 scalar probe linked and exited `0`; the real host
  compositor closure compiled to an archive with zero failures. The deployed
  remote host bridge and pixel-present protocol remain absent, so remote GUI
  presentation and event delivery stay red.

## Remaining runtime gates

- Host GLFW: the real backend/window/input/presentation boundary is green;
  the full Phase-3 closure and static provider link are green. Live execution
  now passes the canonical widget lookup, pure-Simple font provider, initial
  GUI-frame admission, scalar pointer-router, and stable-ID widget mutation
  probes. Packed ARGB presentation and title conversion are now independently
  green. The focused native compositor now admits an external pixel frame and
  reaches an exact nonzero framebuffer sample. The richer exact-demo GUI probe
  now passes Resize token, theme source parsing, theme material checksum
  serialization, exact image resolution, GUI frame construction, external
  admission, and raw compositor readback. The exact-title live demo now has a
  retained non-black screenshot. The new native regression proves VBox row
  geometry is corrupted before Draw IR consumes the returned `WidgetRect[]`;
  the failed in-traversal mirror further narrows it to argument/scalar
  evaluation before or at the recursive layout call.
  Native GLFW pump/pop input is now live-green for key, committed text,
  pointer motion, and button events. Semantic widget mutation and clean
  outer-window close remain RED; Xvfb without a window manager is not valid
  close-request evidence.
- SDL2: its focused native event/window boundary probe is green; the shared
  live WM scenario has not run. SDL3 remains unimplemented.
- QEMU: PS/2 committed text now reaches remote WM IPC through a native-safe
  scalar handoff. Pixel and HDA controller/stream/IRQ source paths share the
  canonical desktop entry, but none has current live guest evidence.
- UNO Q: Debian host validation and the QRB2210 SimpleOS port remain open; the
  STM32U585 lane is not desktop evidence.
- Audio: scalar click playback is green through miniaudio and the focused
  SDL2 queued-device probe. The shared live WM scenario, SDL3, QEMU HDA PCM,
  and board PCM evidence remain open.
- Compiler: the stale Phase 3 binary still fails the isolated runtime-derived
  `i64 as u32` narrowing probe. Current compiler sources contain the cast
  bridge/truncation and cross-block scalar reload fixes. A scoped pure-Simple
  Stage-2-to-compiler refresh (not a bootstrap) now compiles the full closure
  after the three source fixes. The supported positional-entry/runtime-capsule
  recipe avoids the prior link mistake but currently runs away before its first
  cached object. The attempted raw VBox cursor stack is also corrupted before
  it can establish an authoritative row position.
- 2026-07-30 theme checkpoint: a scoped source repair restores the accepted
  native-safe material serializer and projects exact package-CSS semantic
  colors into `ThemePackage`; highest-capability review accepted the corrected
  patch. Runtime/live-host proof is deliberately not claimed because the
  released binary is stale and the external source-matched incremental build
  remains unresolved. CPU/SIMD/Vulkan CPU-composited glass and Web ordered
  shadows remain the next host lanes; x86/ARM QEMU remains postponed until a
  current admitted capsule exists.
- 2026-07-30 CPU glass checkpoint: source and discriminating unit coverage now
  admit concrete CPU/software/CPU-SIMD/Vulkan targets to the bounded CPU
  material compositor. Metal remains the only device-glass request; AUTO/GPU
  remain opaque solid, and Engine2D's result—not producer metadata—owns the
  execution receipt. Highest-capability review accepted the contract on cycle
  3. Live runtime/capture evidence remains unverified.
