# Linux Vulkan Render Log Compare Current Status - 2026-07-02

## Result

Current Linux Vulkan render-log comparison passes with zero blocked gates after
refreshing the canonical browser evidence directories against the repo-local
Vulkan-only RenderDoc build. The direct GUI/Web/2D Vulkan aggregate passes
Simple Vulkan, browser backing, ARGB source, and pairwise pixel comparison
gates, and `build/tools/renderdoc-linux-vulkan-only` produces valid Chrome and
Electron `.rdc` artifacts with `RDOC` magic.

The browser GPU-launcher diagnostic path has moved forward. The shared
RenderDoc helper now passes the detected `build/tools/renderdoc` tree into the
GPU launcher, so the delay/autocapture shims compile against
`renderdoc_app.h` instead of falling back to `/opt/renderdoc`. The RenderDoc
browser flags were also reduced to the same Vulkan essentials used by the
passing browser-backing lane. GPU autocapture metadata now chooses the most
informative `rdoc_autocapture_summary` line instead of the last line, because
Chromium may launch multiple short-lived GPU processes in one log. The Linux
compare and GUI aggregate wrappers also forward the parsed autocapture
`api`/`started`/`finished` lifecycle and start/end source fields.

## Command

```text
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```

## Current Evidence

```text
linux_vulkan_render_log_compare_status=pass
linux_vulkan_render_log_compare_reason=pass
linux_vulkan_render_log_compare_blocked_gate_count=0
linux_vulkan_render_log_compare_blocked_gates=
linux_vulkan_render_log_compare_simple_vulkan_gate_status=pass
linux_vulkan_render_log_compare_browser_backing_gate_status=pass
linux_vulkan_render_log_compare_pairwise_gate_status=pass
linux_vulkan_render_log_compare_argb_source_gate_status=pass
linux_vulkan_render_log_compare_renderdoc_gate_status=pass
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env=build/gui-web-2d-vulkan-env-run-current/evidence.env
linux_vulkan_render_log_compare_gui_web_2d_vulkan_env_file_status=pass
linux_vulkan_render_log_compare_pairwise_status=pass
linux_vulkan_render_log_compare_pairwise_mode=pairwise-argb-diff
linux_vulkan_render_log_compare_renderdoc_simple_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_chrome_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_reason=pass
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_status=pass
linux_vulkan_render_log_compare_renderdoc_chrome_gpu_process_exit_count=0
linux_vulkan_render_log_compare_renderdoc_electron_env_file_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic=RDOC
linux_vulkan_render_log_compare_renderdoc_electron_status=pass
linux_vulkan_render_log_compare_renderdoc_electron_reason=pass
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_status=not-recorded
linux_vulkan_render_log_compare_renderdoc_electron_gpu_process_exit_count=0
```

## Existing Artifacts Checked

- `build/gui-web-2d-vulkan-env-browser-backing/evidence.env`: present
- `build/gui-web-2d-vulkan-env-renderdoc-simple/renderdoc/simple/evidence.env`: present
- `build/renderdoc/canonical-probe/simple/evidence.env`: present
- `build/gui-web-2d-vulkan-env-run-current/evidence.env`: present
- `build/tools/renderdoc-linux-vulkan-only/bin/renderdoccmd`: present, compile-time APIs `Vulkan`
- `build/renderdoc/chrome-vulkan-only-egl-direct-20260702/html/evidence.env`: present, `.rdc` magic `RDOC`
- `build/renderdoc/electron-vulkan-only-egl-direct-20260702/electron-html/evidence.env`: present, no `.rdc`, ARGB helper stops before GPU launcher log
- `build/renderdoc/electron-vulkan-only-dataurl-continue-20260702/electron-html/evidence.env`: present, no `.rdc`, ARGB helper still stops at Electron loader fallback
- `build/renderdoc/electron-vulkan-only-default-display-gpu-20260702/electron-html/evidence.env`: present, `.rdc` magic `RDOC`
- `build/renderdoc/chrome-implicit-layer-default-autocapture/html/evidence.env`: present, refreshed with Vulkan-only RenderDoc, `.rdc` magic `RDOC`
- `build/renderdoc/electron-implicit-layer-default-autocapture/electron-html/evidence.env`: present, refreshed with Vulkan-only RenderDoc display holder, `.rdc` magic `RDOC`
- `build/renderdoc/linux-vulkan-render-log-compare-default-20260702.env`: default compare `status=pass`, `blocked_gate_count=0`

## Status

Do not use `doc/09_report/linux_vulkan_render_log_compare_2026-06-29.md` as
current completion proof on this workspace. Re-run the GUI/Web/2D Vulkan
aggregate and the Chrome/Electron RenderDoc capture lanes before claiming Linux
Vulkan RenderDoc parity is passing. As of this run, the direct aggregate passes,
the canonical Chrome/Electron RenderDoc evidence dirs pass with
`RDOC_HOME=build/tools/renderdoc-linux-vulkan-only`, and the default
`sh scripts/check/check-linux-vulkan-render-log-compare.shs` output reports
`linux_vulkan_render_log_compare_status=pass`. The ARGB helper remains useful
for pixel proof, but is no longer the Electron RenderDoc `.rdc` holder.

## No-Child-Hook Diagnostic

`RDOC_RENDERDOC_HOOK_CHILDREN=0` was tested as a diagnostic only:

```text
build/renderdoc/chrome-implicit-layer-no-child-hook-diagnostic/html/evidence.env
rdoc_chromium_gpu_process_exit_status=pass
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=

build/renderdoc/electron-implicit-layer-no-child-hook-diagnostic/electron-html/evidence.env
rdoc_electron_launch_exit_code=124
rdoc_electron_launch_timed_out=true
rdoc_chromium_gpu_process_exit_status=pass
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
rdoc_capture_magic=
```

This isolates the default crash to RenderDoc child-process hooking, but it is
not passing evidence because neither browser emits a valid `RDOC` artifact.

## GPU-Launcher Trigger Diagnostic

The focused Chrome GPU-launcher path now reaches a real Vulkan instance under
the RenderDoc delay-trigger shim, but still does not emit an `.rdc`:

```text
build/renderdoc/chrome-gpu-delay-trigger-minimal-flags-20260702/html/evidence.env
rdoc_chromium_launch_flags=--no-sandbox --disable-gpu-sandbox --disable-dev-shm-usage --enable-features=Vulkan --use-angle=vulkan
rdoc_gpu_delay_trigger_loaded_count=1
rdoc_gpu_delay_trigger_api_ready_count=1
rdoc_gpu_delay_trigger_vk_create_instance_count=1
rdoc_gpu_delay_trigger_last_vk_instance=non-null
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc

build/renderdoc/chrome-gpu-delay-trigger-target-device-current-20260702/html/evidence.env
rdoc_gpu_delay_trigger_target_device=non-null
rdoc_gpu_delay_trigger_last_vk_instance=non-null
rdoc_gpu_delay_trigger_vk_create_instance_count=1
rdoc_gpu_delay_trigger_is_capturing_after_start=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc

build/renderdoc/chrome-gpu-delay-trigger-trigger-mode-current-20260702/html/evidence.env
rdoc_gpu_delay_trigger_mode=trigger
rdoc_gpu_delay_trigger_capture_count=1
rdoc_gpu_delay_trigger_target_device=non-null
rdoc_gpu_delay_trigger_last_vk_instance=non-null
rdoc_gpu_delay_trigger_vk_create_instance_count=1
rdoc_gpu_delay_trigger_num_captures_after=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc

build/renderdoc/chrome-gpu-autocapture-trace-20260702/html/evidence.env
rdoc_gpu_autocapture_loaded_count=1
rdoc_gpu_autocapture_api=1
rdoc_gpu_autocapture_started=1
rdoc_gpu_autocapture_finished=1
rdoc_gpu_autocapture_start_source=delay
rdoc_gpu_autocapture_end_source=delay
rdoc_gpu_autocapture_vk_create_instance_count=1
rdoc_gpu_autocapture_vk_create_device_count=0
rdoc_gpu_autocapture_vk_enum_physical_device_count=2
rdoc_gpu_autocapture_vk_enum_physical_device_last_count=3
rdoc_gpu_autocapture_vk_get_physical_device_properties_count=3
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=0
rdoc_gpu_autocapture_vk_enum_device_extension_count=0
rdoc_gpu_autocapture_submit_count=0
rdoc_gpu_autocapture_present_count=0
rdoc_gpu_autocapture_egl_swap_count=0
rdoc_gpu_autocapture_egl_initialize_success_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc

build/renderdoc/chrome-gpu-autocapture-egl-getproc-alias-20260702/html/evidence.env
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_autocapture_loaded_count=7
rdoc_gpu_autocapture_api=0
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_vk_create_instance_count=0
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc

build/renderdoc/chrome-gpu-autocapture-device-properties-long-20260702/html/evidence.env
rdoc_gpu_autocapture_vk_enum_physical_device_count=2
rdoc_gpu_autocapture_vk_enum_physical_device_last_count=3
rdoc_gpu_autocapture_vk_get_physical_device_properties_count=3
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=0
rdoc_gpu_autocapture_vk_enum_device_extension_count=0
rdoc_autocapture_physical_device_properties=index:1 type:2 vendor:4318 device:8752 api:4210688 driver:2434761728 name:NVIDIA_RTX_A6000
rdoc_autocapture_physical_device_properties=index:2 type:2 vendor:4318 device:7682 api:4210688 driver:2434761728 name:NVIDIA_TITAN_RTX
rdoc_autocapture_physical_device_properties=index:3 type:4 vendor:65541 device:0 api:4202496 driver:104865800 name:llvmpipe_(LLVM_20.1.2,_256_bits)

build/renderdoc/chrome-gpu-autocapture-query2-boundary-20260702/html/evidence.env
rdoc_gpu_autocapture_vk_get_physical_device_properties_count=3
rdoc_gpu_autocapture_vk_get_physical_device_properties2_count=3
rdoc_gpu_autocapture_vk_get_physical_device_features2_count=0
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=0
rdoc_gpu_autocapture_vk_get_physical_device_queue_family2_count=0
rdoc_gpu_autocapture_vk_enum_device_extension_count=0

build/renderdoc/chrome-gpu-autocapture-properties2-pnext-xvfb-20260702/html/evidence.env
rdoc_chrome_display_mode=gpu-autocapture

build/renderdoc/chrome-gpu-autocapture-properties2-pnext-xvfb-20260702/html/gpu-launcher.log
rdoc_autocapture_physical_device_properties2=index:1 type:2 vendor:4318 device:8752 api:4210688 driver:2434761728 name:NVIDIA_RTX_A6000
rdoc_autocapture_physical_device_properties2_pnext=index:1 depth:0 stype:1000071004
rdoc_autocapture_physical_device_properties2_pnext=index:1 depth:1 stype:1000196000
rdoc_autocapture_physical_device_driver_properties=index:1 driver_id:4 name:NVIDIA info:580.126.16 conformance:1.4.1.3
rdoc_autocapture_physical_device_properties2=index:2 type:2 vendor:4318 device:7682 api:4210688 driver:2434761728 name:NVIDIA_TITAN_RTX
rdoc_autocapture_physical_device_driver_properties=index:2 driver_id:4 name:NVIDIA info:580.126.16 conformance:1.4.1.3
rdoc_autocapture_physical_device_properties2=index:3 type:4 vendor:65541 device:0 api:4202496 driver:104865800 name:llvmpipe_(LLVM_20.1.2,_256_bits)
rdoc_autocapture_physical_device_driver_properties=index:3 driver_id:13 name:llvmpipe info:Mesa_25.2.8-0ubuntu0.24.04.2_(LLVM_20.1.2) conformance:1.3.1.1

build/renderdoc/chrome-gpu-autocapture-id-properties-20260702/html/gpu-launcher.log
rdoc_autocapture_instance_version=result:0 version:4211036
rdoc_autocapture_create_instance_extension_count=0
rdoc_autocapture_create_instance_result=0 instance:1
rdoc_autocapture_physical_device_id_properties=index:1 device_uuid:00833ff29a6b95fa66ce2e1c96090b11 driver_uuid:614d8318a68d5ceea8a05eccd73f659a luid:0000000000000000 node_mask:1 luid_valid:0
rdoc_autocapture_physical_device_properties2=index:1 type:2 vendor:4318 device:8752 api:4210688 driver:2434761728 name:NVIDIA_RTX_A6000

build/renderdoc/chrome-gpu-autocapture-id-properties-clear-layer-20260702/html/gpu-launcher.log
rdoc_autocapture_instance_version=result:0 version:4211036
rdoc_autocapture_create_instance_extension_count=6
rdoc_autocapture_create_instance_extension=ordinal:5 name:VK_KHR_xcb_surface
rdoc_autocapture_physical_device_id_properties=index:1 device_uuid:00833ff29a6b95fa66ce2e1c96090b11 driver_uuid:614d8318a68d5ceea8a05eccd73f659a luid:0000000000000000 node_mask:1 luid_valid:0
rdoc_autocapture_physical_device_properties2=index:1 type:2 vendor:4318 device:8752 api:4211000 driver:2434761728 name:NVIDIA_RTX_A6000

build/renderdoc/chrome-gpu-autocapture-clear-layer-20260702/html/evidence.env
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_gpu_autocapture_vk_create_device_count=2
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=8
rdoc_gpu_autocapture_vk_enum_device_extension_count=10
rdoc_gpu_autocapture_submit_count=8
rdoc_gpu_autocapture_present_count=5

build/renderdoc/chrome-gpu-autocapture-clear-instance-layers-20260702/html/evidence.env
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=1
rdoc_gpu_autocapture_vk_create_device_count=0
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=0

build/renderdoc/chrome-gpu-autocapture-clear-renderdoc-enable-20260702/html/evidence.env
rdoc_gpu_launcher_vk_instance_layers=VK_LAYER_RENDERDOC_Capture
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_gpu_autocapture_vk_create_device_count=0
rdoc_gpu_autocapture_vk_get_physical_device_queue_family_count=0

build/renderdoc/chrome-gpu-autocapture-clear-instance-and-enable-20260702/html/evidence.env
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_gpu_autocapture_status=not-started
rdoc_gpu_autocapture_vk_create_device_count=2
rdoc_gpu_autocapture_submit_count=8
rdoc_gpu_autocapture_present_count=5

build/renderdoc/chrome-gpu-autocapture-clear-both-dlopen-late-20260702/html/evidence.env
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_gpu_autocapture_api=1
rdoc_gpu_autocapture_start_source=submit
rdoc_gpu_autocapture_end_source=submit
rdoc_gpu_autocapture_vk_create_device_count=2
rdoc_gpu_autocapture_submit_count=7
rdoc_gpu_autocapture_present_count=4
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
build/renderdoc/chrome-gpu-autocapture-clear-both-dlopen-late-20260702/html/gpu-launcher.log
rdoc_autocapture_end=submit ok=0 submit=2 present=0 egl_swap=0

build/renderdoc/electron-gpu-autocapture-clear-both-dlopen-late-20260702/electron-html/evidence.env
rdoc_gpu_launcher_vk_instance_layers=
rdoc_gpu_launcher_enable_vulkan_renderdoc_capture=
rdoc_gpu_autocapture_api=1
rdoc_gpu_autocapture_start_source=submit
rdoc_gpu_autocapture_end_source=present
rdoc_gpu_autocapture_vk_create_device_count=2
rdoc_gpu_autocapture_submit_count=4
rdoc_gpu_autocapture_present_count=1
rdoc_capture_status=fail
rdoc_capture_reason=missing-rdc
build/renderdoc/electron-gpu-autocapture-clear-both-dlopen-late-20260702/electron-html/gpu-launcher.log
rdoc_autocapture_end=present ok=0 submit=1 present=1 egl_swap=0

build/renderdoc/chrome-gpu-autocapture-clear-layer-preload-rdoc-20260702/html/evidence.env
rdoc_gpu_launcher_clear_renderdoc_layer=1
rdoc_chromium_gpu_process_exit_status=fail
rdoc_chromium_gpu_process_exit_codes=139
rdoc_gpu_autocapture_status=missing-summary
build/renderdoc/chrome-gpu-autocapture-clear-layer-preload-rdoc-20260702/html/gpu-launcher.log
renderdoc_gpu_launcher_preload_renderdoc=1
```

The next concrete blocker moved on July 2. Stock RenderDoc with GL/GLES/EGL
enabled still blocks the browser GPU child before the WSI path: the shim sees
physical-device properties, but no features2, queue-family,
device-extension, `vkCreateDevice`, submit/present, EGL swap, or successful EGL
initialize return. Clearing the RenderDoc layer while leaving the shim active
reaches `vkCreateDevice`, submit, and present, proving Chromium and the shim can
see the device/frame boundary. Clearing only `VK_INSTANCE_LAYERS` still blocks,
and clearing only `ENABLE_VULKAN_RENDERDOC_CAPTURE` still blocks. Clearing both
lets Chromium render through Vulkan but leaves the RenderDoc API unavailable.

The repo-local Vulkan-only RenderDoc build now installs successfully into
`build/tools/renderdoc-linux-vulkan-only` with compile-time API support
`Vulkan` only. The setup wrapper can consume local dev-package headers from
`build/tools/renderdoc-local-sysroot`; this was used for `xcb_keysyms.h` and
`X11/Xlib-xcb.h` without sudo. Focused Chrome evidence at
`build/renderdoc/chrome-vulkan-only-egl-direct-20260702` produced
`html/gpu_chrome_capture.rdc` with `RDOC` magic. Its GPU launcher log reaches
`rdoc_autocapture_egl_get_platform_display`,
`rdoc_autocapture_egl_initialize`, and later WSI-enabled
`rdoc_autocapture_create_instance_extension_count=5/6`, confirming that the
Vulkan-only build removes the stock EGL-hook blocker for Chrome.

Electron now uses the existing display holder for RenderDoc `.rdc` evidence.
`build/renderdoc/electron-vulkan-only-default-display-gpu-20260702` produced
`electron-html/electron_gpu_capture.rdc` with `RDOC` magic, while the stage log
completed `before-load-data-url`, `after-load-data-url`, `before-hold`, and
`after-hold`. The older ARGB-helper probes under
`electron-vulkan-only-egl-direct-*` and `electron-vulkan-only-dataurl-*` still
demonstrate why ARGB capture should remain in the separate pixel-proof lane:
they can time out before the GPU-launcher/autocapture telemetry exists.

Do not wrap `dlsym("EGL_GetProcAddress")` as an alias for
`eglGetProcAddress` in the preload shim. That diagnostic regressed Chrome to
GPU process exit `139` before the RenderDoc API became available.

Use the canonical paths consumed by
`scripts/check/check-linux-vulkan-render-log-compare.shs`:

```sh
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-browser-backing \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --browser-backing
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-run-current \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-env-renderdoc-simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple
RDOC_OUTPUT_DIR=build/renderdoc/chrome-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-html
RDOC_OUTPUT_DIR=build/renderdoc/electron-implicit-layer-default-autocapture \
  scripts/tool/renderdoc-evidence.shs capture-electron-html
sh scripts/check/check-linux-vulkan-render-log-compare.shs
```
