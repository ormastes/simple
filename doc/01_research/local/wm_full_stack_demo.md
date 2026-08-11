<!-- codex-research -->
# WM Full-Stack Demo — Local Research

Date: 2026-07-29

## Decision

The next executable target is the user-selected Linux/GLFW Phases 0–6
vertical slice plus isolated compiler regressions. SDL2/SDL3, host audio,
QEMU HDA, and UNO Q QRB2210 remain consumers of the same contracts; they are
not completion claims for this slice.

This lane extends, rather than replaces:

- `wm_gui_web_2d_host_env_hardening`
- `simple_wm_host_simpleos_fullscreen`
- `sound_engine`
- `rendering_inside_rendering`
- `simpleos_qemu_host_gpu_2d`

## Confirmed Root Integration Gap

The SimpleOS shell creates real `UITree` values and sends them through
`Compositor.create_window_with_tree()`:

1. `src/os/desktop/shell.spl:_create_materialized_window` creates the tree.
2. `src/os/compositor/compositor.spl:create_window_with_tree` calls
   `update_window_tree`.
3. `WindowSurface.session: any` stores the tree.
4. `Compositor.render_all()` never reads `session`.
5. Every visible client body is rendered by
   `render_simple_web_content(..., s.content_html)`.

A GUI session can therefore exist without becoming visible or interactive.
The hosted compositor has the same producer collapse in a different shape:
`HostedWindow` retains only text content and `_taskbar_render_input()` creates a
Simple Web frame for every non-browser window.

## Existing Owners to Reuse

| Concern | Existing owner | Current gap |
|---|---|---|
| Canonical compositor input | `common.ui.window_scene.WmContentFrame` | Hosted admission is named and constrained as external Web only |
| GUI frame adapter | `common.ui.wm_gui_content_frame` | Not connected to the production WM |
| Nested frames | `common.ui.window_scene_draw_ir` | No `RenderSurface` widget or child-surface registry |
| GUI lowering | `common.ui.widget_draw_ir` | Not called by production WM content ownership |
| GUI interaction | `nogc_sync_mut.ui.session.UISession` and `common.ui.event` | Platform events are not routed into a retained session |
| Host presentation | `nogc_sync_mut.ui.gui_renderer` and hosted compositor | Winit-only facade; text/modifier data is partially discarded |
| Lifecycle | `os.compositor.wm_action_lifecycle` and `HostCompositor` | State authority is duplicated; close/pin cleanup is incomplete |
| Taskbar schema | `common.ui.taskbar_model` | Host model returns no pinned apps; existing save helper is not production persistence |
| Sound facade | `nogc_sync_mut.engine.audio.sound_engine` | Records commands only |
| Host PCM | `runtime_audio.c`, `audio_sffi`, `AudioManager` | Separate unsafe raw-pointer API, omitted from default hosted runtime bundle |
| QEMU audio | `os.drivers.audio.hda_controller` | No PCI/BAR/DMA/codec/IRQ/refill boot integration |
| UNO Q | STM32U585 adapter and QRB2210-hosted checks | No native QRB2210 SimpleOS boot/display/HID/audio port |

`WmContentFrame` already accepts GUI and Simple Web origins, checks dimensions,
revisions, pixel count, and checksum, and carries nested parent-relative
offsets. `wm_content_frame_web_provenance_valid()` intentionally leaves
non-Web producers to their own contracts. A new parallel compositor or image
format is unnecessary.

## Event Findings

- The winit SFFI already exports committed-text bytes and a Shift flag, but
  `GuiRenderer.GuiEvent` does not retain text and does not independently retain
  Ctrl, Alt, or Super.
- Hosted input drains into WM/Web state, not `UISession`.
- The current SDL2 C bridge is real, but its Simple wrapper can report requested
  rather than consumed event counts and treats unsupported operations as
  success.
- A pollable normalized queue is the smallest common boundary for GLFW, SDL,
  deterministic tests, and future SimpleOS application windows.

The native boundary must remain scalar: generation-counted handles, fixed event
records, a bounded queue, text arena handles, explicit status codes, and
out-parameters. High-level `Result` values belong above that boundary.

## Rendering Findings

- `widget_tree_to_draw_ir_with_theme()` already performs layout and lowers
  panels, text, buttons, text fields/carets, images, and clipped scrolling.
- `shared_wm_scene_draw_ir_composition_with_content()` already composes top and
  nested `WmContentFrame` values through the shared Engine2D lane.
- `wm_gui_content_frame_from_pixels()` already creates fail-closed GUI frames
  using the shared checksum.
- Existing showcase applications prove pieces independently, but no one live
  application proves GUI + Web + 2D + WM lifecycle through one content-frame
  route.

The minimum change is explicit content identity at window authority, followed
by dispatch to existing GUI, Web, or pixel producers. The production route
must not stringify an opaque tree or use Simple Web as the universal fallback.

## Sound and Board Findings

The current `SoundEngine` is a command log. Pure-Simple WAV decode/encode and
synthesis already exist, while `runtime_audio.c` provides a real miniaudio
engine but exposes raw `ma_sound*` values as integers. Repeated stop/query can
therefore become use-after-free, natural completion is not collected, and
mixed-output capture does not exist.

The smallest later host-audio slice is a fixed 48-kHz stereo-f32 miniaudio
engine with one bounded generation-handle table, idempotent stop/destroy,
finished-voice collection, and mixed-frame count/checksum. SDL and HDA should
consume a later `render_pcm_frames` seam only after this slice is proven.

The current UNO Q SimpleOS work targets the STM32U585 MCU. A desktop result
requires a separate `unoq_qrb2210_simpleos_port` lane. Existing QRB2210 evidence
that hosts x86 SimpleOS QEMU under Debian is useful host evidence, but is not a
native QRB2210 SimpleOS result.

## Compiler Hardening Findings

Existing reusable gates include:

- `scripts/check/check-native-seed-parity.shs`
- `test/fixtures/compiler/native_trait_optional_struct_return.spl`
- `scripts/check/check-cranelift-aot-aggregates.shs`
- `test/fixtures/compiler/stage4_struct_enum_array_probe.spl`
- `test/01_unit/lib/common/ui/theme_package_wire_native_abi_probe_spec.spl`
- `test/01_unit/compiler/backend/linker/sym_resolver_spec.spl`

Current gaps are runtime proof for compound Option/Result aggregate payloads,
nested aggregate returns, arrays inside returned structs, aggregate module
globals on `x86_64-unknown-none`, and live entry-closure rejection of fabricated
`lib__*`/`os__*` weak stubs.

The Phase 3 pixel controls now give direct evidence for the WM workaround:
class-held `[u32]` access through a receiver remains RED, while the replacement
raw allocation with scalar address/count fields passes. The compositor pixel
store therefore owns raw registry/pixel memory behind generation handles and
does not pass pixel arrays through the freestanding render method boundary.
Its pitched ARGB32 blit now uses the repaired pure `simple-core`
`rt_ptr_write_i32`, which writes four bytes rather than the prior eight-byte
overwrite. An archive-linked Phase 3 probe verifies preserved neighboring
bytes, blit placement, pitch handling, and fail-closed destination bounds.

The host GLFW C boundary is also runtime-proven. A distro GLFW runtime
extracted under `build/` plus Xvfb produced a real OpenGL window, two ARGB
frames, clipboard round-trip, and native X11 key/text/pointer/button events;
destroy returned the live-window count to zero. Presentation now reuses a
per-window OpenGL texture and grow-only staging buffer; the second frame uses
`glTexSubImage2D` without another allocation. This does not substitute for the
Skia-blocked full WM scene capture.

Compiler MIR/HIR files are currently modified by another active lane. This work
must add isolated fixtures/gates without folding or rewriting those changes.

## Minimum Implementation Order

1. Add fail-closed runtime-truth and compiler regression tests.
2. Add the normalized event/window contract and deterministic headless queue.
3. Add GLFW as an adapter into that contract and existing compositor.
4. Generalize hosted external-frame admission from Web-only to valid
   `WmContentFrame` producers.
5. Connect retained GUI session rendering and event dispatch.
6. Add the minimal nested render-surface primitive.
7. Finish lifecycle, taskbar app pin persistence, close cleanup, and one live
   GLFW evidence scenario.

No SDL, HDA, or QRB2210 gate may be marked complete from source inspection.

## 2026-07-29 Phase 3 implementation note

The host runtime now uses synchronized generation handles and can consume
owned 48-kHz stereo PCM. The UI click generator writes deterministic samples
behind a scalar raw address, and the host device copies them into
miniaudio-owned f32 storage, removing the earlier Simple-array
`gen_sine`/`apply_adsr` aggregate-return chain.

The isolated `build/aggfix/stage3/simple` sound probe still takes the
`play_ui_click()` success branch even when a directly constructed engine has
`device_started=false`. A smaller receiver-plus-local-buffer compiler control
passes, narrowing the defect to the larger SoundEngine method or boolean-return
lowering. The standalone raw click generator/checksum now passes Phase 3 and
is the permitted QEMU/QRB2210 producer boundary; the larger class remains a
host compatibility facade until its receiver regression is repaired.

A linked host runtime smoke also opened miniaudio, submitted raw stereo PCM,
observed a generation-counted live playback handle, stopped it, and verified
the live-handle count returned to zero. QEMU HDA and board device proof remain
separate gates.

Taskbar pin ownership now uses stable `app_id` values and the shared VFS at
`/SYS/TASKBAR.PIN`. Its bounded versioned wire codec passes an isolated Phase 3
native probe; the shell integration has a focused mounted-DBFS persistence
spec. A live SimpleOS restart remains required before durable persistence is
runtime-proven.
