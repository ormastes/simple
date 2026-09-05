# Electron RenderDoc Vulkan Widget Capture Launch Diagnostics - 2026-06-28

## Status

Open blocker for the GUI/web/2D RenderDoc hardening goal.

## Summary

Electron Chromium can render the generated GUI widget fixture to a nonblank
ARGB artifact under Vulkan/ANGLE flags, but this Linux host still does not
produce the required Electron `.rdc` file for widget RenderDoc completion.

The normal child-hook capture path records repeated Electron GPU process exits:

- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_status=fail`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_count=6`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_codes=139`
- `gui_widget_renderdoc_goal_electron_gate_gpu_process_exit_reason=gpu-process-exited-unexpectedly`

A focused no-child-hook diagnostic was also tried:

```sh
RDOC_RENDERDOC_HOOK_CHILDREN=0 \
RDOC_CAPTURE_TIMEOUT_SECS=20 \
RDOC_OUTPUT_DIR=build/renderdoc/electron-widget-no-child-hook \
RDOC_HTML_PATH="$PWD/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html" \
timeout 45s scripts/tool/renderdoc-evidence.shs capture-electron-html
```

That path is worse on this host:

- `rdoc_renderdoc_hook_children=0`
- `rdoc_electron_launch_exit_code=124`
- `rdoc_electron_launch_timed_out=true`
- `rdoc_electron_argb_status=missing`
- `rdoc_capture_status=fail`
- `rdoc_capture_reason=missing-rdc`

## Completion Requirement

Do not mark Electron widget RenderDoc complete until a prepared host produces a
regular Electron `.rdc` capture whose first bytes are `RDOC`, while also keeping
the widget fixture ARGB proof nonblank and Chromium Vulkan/ANGLE fields present.

## Next Checks

- Try a prepared Linux GUI host with RenderDoc and Electron outside this stale
  session state.
- Keep `RDOC_RENDERDOC_HOOK_CHILDREN=1` as the default; `0` is diagnostic only
  and currently times out without ARGB or `.rdc`.
- If retrying Electron flags, reject `--in-process-gpu` unless it still proves
  Vulkan and emits a valid `.rdc`.
