# Linux Hosted WM Live Window Specification

> This scenario hardens the Linux hosted SimpleOS WM entry. The entry must create a real winit-hosted window, keep it windowed rather than fullscreen, and present the first frame through the Simple Web hosted WM path.

<!-- sdn-diagram:id=linux_hosted_wm_live_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linux_hosted_wm_live_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linux_hosted_wm_live_window_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linux_hosted_wm_live_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Hosted WM Live Window Specification

This scenario hardens the Linux hosted SimpleOS WM entry. The entry must create a real winit-hosted window, keep it windowed rather than fullscreen, and present the first frame through the Simple Web hosted WM path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/gui_hardening_current_plan/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/03_system/gui/linux_hosted_wm_live_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario hardens the Linux hosted SimpleOS WM entry. The entry must create
a real winit-hosted window, keep it windowed rather than fullscreen, and present
the first frame through the Simple Web hosted WM path.

## Acceptance Criteria

- `src/os/hosted/hosted_entry.spl` creates `SimpleOS Shared Hosted WM` at
  1024x720 through `rt_winit_window_new`.
- The entry emits a window-created marker with `mode=windowed` and
  `fullscreen=false` only after `rt_winit_window_new` returns a nonzero handle.
- The entry emits a frame-presented marker with `renderer=simple-web` after
  `HostCompositor.render_frame()`.
- The live wrapper uses a GUI-enabled driver and reports
  `linux_hosted_wm_live_window_status=pass`.

## Syntax

Run the source-contract SPipe spec with:

```bash
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/gui/linux_hosted_wm_live_window_spec.spl \
  --mode=interpreter --clean --format json
```

Run the live Linux hosted-window evidence wrapper with:

```bash
BUILD_DIR=build/linux-hosted-wm-live-window-evidence-current \
REPORT_PATH=build/linux-hosted-wm-live-window-evidence-current/report.md \
LINUX_HOSTED_WM_LIVE_TIMEOUT_SECS=25 \
sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs
```

The wrapper requires a GUI-enabled Simple driver. It searches, in order:

```text
src/compiler_rust/target/gui/debug/simple
src/compiler_rust/target/gui/release/simple
src/compiler_rust/target/debug/simple
src/compiler_rust/target/release/simple
```

Each candidate must be executable and contain the `rt_winit_event_loop_new`
runtime symbol. If no candidate exists, build one with:

```bash
cd src/compiler_rust
cargo build -p simple-driver --features gui
```

## Examples

A passing wrapper run emits these fields:

```text
linux_hosted_wm_live_window_status=pass
linux_hosted_wm_live_window_reason=linux-windowed-winit-frame-presented
linux_hosted_wm_live_window_window_marker=pass
linux_hosted_wm_live_window_frame_marker=pass
```

The hosted WM stdout must contain:

```text
[hosted-wm] window-created backend=winit mode=windowed fullscreen=false width=1024 height=720 title=SimpleOS Shared Hosted WM
[hosted-wm] frame-presented renderer=simple-web host=linux-windowed width=1024 height=720
```

## Evidence Model

The source-contract spec and the live wrapper intentionally check different
things.

The SPipe spec is quick and deterministic. It verifies that the hosted entry
still requests a 1024x720 winit window, keeps the launch windowed, seeds the
shared MDI scene, and presents through `HostCompositor.render_frame()`.

The wrapper is the live Linux proof. It launches `src/os/hosted/hosted_entry.spl`
with the GUI-enabled driver, waits for the first-frame marker, terminates the
process, and writes a report. The marker is printed only after the winit window
handle is nonzero and the frame has been rendered.

GNOME Wayland can hide native Wayland windows from X11-only tools such as
`xdotool` and ImageMagick `import`. The wrapper therefore treats the winit
runtime marker as authoritative and does not require Xwayland window discovery.
If a future compositor-inspection helper is available, it can be added as
supporting evidence without weakening the marker contract.

## Failure Diagnostics

- `missing-gui-enabled-driver` means the GUI driver was not built or does not
  contain `rt_winit_event_loop_new`.
- `missing-windowed-frame-marker` means the hosted entry did not prove both the
  non-fullscreen winit window and the Simple Web frame presentation.
- A missing `window-created` marker usually points at `rt_winit_window_new`
  returning zero or failing before the hosted compositor is initialized.
- A missing `frame-presented` marker means the window was created but the shared
  MDI scene did not render through the hosted compositor.
- Stderr warnings about deprecated generic syntax or runtime-family layering are
  not accepted as pass evidence; they are diagnostic noise unless the wrapper
  report status is `pass`.

## Relationship To QEMU

The Linux hosted path is windowed by design. It runs inside the host desktop
session and must not request fullscreen. The SimpleOS QEMU path is separate:
`test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` boots the x86_64
kernel, captures the 1024x768 framebuffer through QMP `pmemsave`, samples the
Simple Web panel pixels, and injects keyboard input to prove the frame changes.

Together the two gates cover the user-facing requirement:

- Linux host: visible hosted WM path through winit, windowed, Simple Web frame
  presented.
- QEMU SimpleOS: fullscreen guest framebuffer path, Simple Web panel renderer,
  Engine2D blit, QMP pixels, and input-driven framebuffer delta.

## Operator Notes

Do not run the live wrapper from inside this SPipe spec. Nested GUI launches can
be unstable under CI, Wayland, and test-runner process capture. Run the wrapper
as a separate evidence command and use its report as the authoritative live
Linux proof.

Do not replace this path with the offscreen hosted WM capture wrapper. The
offscreen wrapper is useful for deterministic pixel metrics, but it does not
prove that the interactive hosted WM entry opens a winit window.

**Requirements:** N/A
**Plan:** .spipe/gui_hardening_current_plan/state.md
**Design:** doc/04_architecture/ui/simple_gui_stack.md
**Research:** N/A

## Scenarios

### Linux hosted WM live window

#### keeps the hosted SimpleOS WM windowed and Simple Web rendered

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = file_read("src/os/hosted/hosted_entry.spl")
expect(entry).to_contain("val WINDOW_WIDTH: i32 = 1024")
expect(entry).to_contain("val WINDOW_HEIGHT: i32 = 720")
expect(entry).to_contain("val WINDOW_TITLE: text = \"SimpleOS Shared Hosted WM\"")
expect(entry).to_contain("rt_winit_window_new(el, WINDOW_WIDTH.to_i64(), WINDOW_HEIGHT.to_i64(), WINDOW_TITLE)")
expect(entry).to_contain("[hosted-wm] window-created backend=winit mode=windowed fullscreen=false")
expect(entry).to_contain("[hosted-wm] frame-presented renderer=simple-web host=linux-windowed")
expect(entry).to_contain("seed_host_compositor_shared_mdi(comp)")
expect(entry).to_contain("comp.render_frame()")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
