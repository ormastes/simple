# WM / GUI / Web / 2D Dependency Audit

**Date:** 2026-08-05 · **Lane:** read-only audit · **Status:** evidence, no fixes applied.

## Portability contract under test

> If Simple 2D (rendering + event delivery) runs on SimpleOS, the WM runs on SimpleOS.
> Nothing else may be a precondition.

Every host/OS edge is scored against one question: **would the WM fail to run on
SimpleOS if this were unavailable?**

| Bucket | Definition |
|---|---|
| **A** | Rendering lane — engine2d / browser_engine / GPU backends / paint / ui model-layout-style, plus pure computation. Legitimate. |
| **B** | 2D **surface/presentation** or **input event delivery** only. Legitimate, but must route through ONE interface. |
| **C** | Everything else, including things that look benign (timers, clipboard, display enumeration, CPU-feature probes). Each is a **hidden precondition** that breaks the contract. |
| I / R / E | Bookkeeping, not deps: `I` intra-scope import, `R` language runtime primitive (`rt_alloc`, `rt_memcpy`, `rt_ptr_*`, `rt_math_*`), `E` ECS (MDSOC+ sanctioned). |

## Headline

| Metric | Count |
|---|---|
| Files in scope (`.spl`, vendored excluded) | **454** (~162,000 lines) |
| **Bucket C violations** | **184** — 135 import edges + 49 `extern fn` decls |
| **Bucket B host/OS surface (the interface-lane input)** | **5 edges / 3 distinct capabilities** |
| Bucket A (rendering + pure) edges | 178 imports + 53 externs |
| Intra-scope edges | 930 |
| Runtime primitives (neutral) | 55 externs |

**The headline result is the asymmetry.** The rendering-lane dependency is real and
dominant, but the *legitimate* host surface is almost nonexistent (5 edges), while the
*illegitimate* one is 184 edges. The WM/GUI/web/2D surface is not one interface away
from portable — it currently assumes an entire POSIX-shaped host.

---

## Bucket C — violations, by assumed SimpleOS capability

This is the port list: each row is a capability SimpleOS would otherwise have to provide.

| Category | Count | Capability the code assumes exists |
|---|---|---|
| io | 41 | generic host I/O runtime |
| os | 28 | assorted os.* / std.os host services |
| timer | 22 | monotonic + wall clock (rt_time_*/rt_sleep_nanos) |
| net | 21 | TCP/TLS/DNS network stack |
| io-runtime | 13 | generic host I/O runtime (std.io_runtime) |
| ffi | 12 | raw FFI bridge |
| tooling-cli | 11 | argv/CLI + logging host |
| env | 7 | process environment variables |
| host-capability | 7 | CPU feature / arch / pointer-width detection |
| syscall-raw | 4 | SimpleOS raw syscall ABI + klog |
| process | 4 | process spawn + wait |
| mmio/kernel | 4 | raw MMIO reads against a device aperture |
| fs | 4 | filesystem (open/read/write/exists) |
| dynamic-link | 3 | dynamic loader (dlopen/dlsym) + WFFI |
| entropy | 2 | random / entropy source |
| compiler | 1 | in-process compiler backend at runtime |

### By area

| Area | C edges |
|---|---|
| src/app/wm_compare | 77 |
| src/lib/gc_async_mut/gpu/browser_engine | 55 |
| src/lib/gc_async_mut/gpu/engine2d | 33 |
| src/os/services/wm | 9 |
| src/lib/nogc_sync_mut/play/wm | 4 |
| src/app/wm_showcase | 3 |
| src/lib/common/ui | 2 |
| src/lib/nogc_async_mut/wm | 1 |

### Reading these numbers

- `src/app/wm_compare` (77) is a **measurement/comparison harness**, not shipped WM.
  Its fs/process/env/CLI use is arguably in-role for a harness — but it lives inside the
  audited surface and imports the same modules, so under the stated contract it is
  counted. Excluding it drops the violation count to **107**.
- `src/lib/gc_async_mut/gpu/browser_engine` (55) is dominated by the **HTTP/WebSocket
  stack** (`net/h1_client.spl`, `net/websocket_client.spl`, `net/cache.spl`). A browser
  engine needing a network stack is unsurprising, but it means `browser_engine` cannot
  be a pure rendering-lane consumer — the *fetch* half must be split from the *render*
  half before the 2D lane is portable.
- `src/os/services/wm` (9) is the **SimpleOS-side implementation**
  (`os.userlib.syscall_raw`, `os.kernel.log.klog_api`, `mmio_read8/16/32/64`). It is a
  backend, not a consumer. Its syscall/MMIO surface is exactly what the single interface
  should hide — listed as C so the interface lane sees the full ABI it must cover.
- `src/lib/nogc_async_mut/wm` (1) is the cleanest module in the audit: **one** violation
  (`rt_time_now_micros` in `wm_optimization.spl`) and otherwise zero external edges.
  `compositor.spl`, `input.spl`, `service.spl` have **no `use` and no `extern` at all**.

### C violations — import edges (135)

- `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:28` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:29` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:33` -> `app.io.mod` **[io]**
- `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:35` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/_HtmlCompat/capture_and_compare.spl:36` -> `app.io.env_ops` **[io]**
- `src/app/wm_compare/_HtmlCompat/ppm_and_widget_pixels.spl:24` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/_HtmlCompat/ppm_and_widget_pixels.spl:25` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/_HtmlCompat/report_and_fixture.spl:24` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/_HtmlCompat/report_and_fixture.spl:25` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/_HtmlCompat/report_and_fixture.spl:30` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:22` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:23` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:25` -> `os.compositor.wm_scene` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:26` -> `os.compositor.electron_capture` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:27` -> `os.compositor.qemu_capture` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:28` -> `os.compositor.screenshot_compare` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:32` -> `os.compositor.perceptual_compare` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:33` -> `os.compositor.tolerance_profile` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:36` -> `os.compositor.diff_export` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:224` -> `os.compositor.wm_scene` **[os]**
- `src/app/wm_compare/_WmCompareMain/capture_io.spl:483` -> `os.compositor.screenshot_compare` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:22` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:23` -> `std.cli.log_modes` **[tooling-cli]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:25` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:27` -> `os.compositor.wm_scene` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:28` -> `os.compositor.electron_capture` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:29` -> `os.compositor.qemu_capture` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:30` -> `os.compositor.screenshot_compare` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:34` -> `os.compositor.perceptual_compare` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:35` -> `os.compositor.tolerance_profile` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:38` -> `os.compositor.diff_export` **[os]**
- `src/app/wm_compare/_WmCompareMain/run_modes.spl:127` -> `os.compositor.screenshot_compare` **[os]**
- `src/app/wm_compare/backend_measurement_capture.spl:5` -> `compiler.backend.gpu_portable_compute` **[compiler]**
- `src/app/wm_compare/backend_measurement_capture.spl:9` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/backend_measurement_cuda.spl:11` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/backend_measurement_export.spl:9` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/backend_measurement_export.spl:10` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/backend_measurement_export.spl:11` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/backend_measurement_opencl.spl:11` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/backend_measurement_software_export.spl:11` -> `std.nogc_sync_mut.io_runtime` **[io-runtime]**
- `src/app/wm_compare/backend_measurement_software_export.spl:12` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/backend_measurement_software_export.spl:13` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/backend_parity.spl:21` -> `os.drivers.framebuffer.fb_driver` **[os]**
- `src/app/wm_compare/backend_parity.spl:22` -> `os.compositor.browser_compositor_backend` **[os]**
- `src/app/wm_compare/export_site_corpus.spl:3` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/golden_gate.spl:22` -> `std.nogc_sync_mut.io.dir_ops` **[io]**
- `src/app/wm_compare/golden_gate.spl:23` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/app/wm_compare/golden_gate.spl:24` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_compare/golden_gate.spl:25` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/graphical_backend_equality.spl:3` -> `os.compositor.screenshot_compare` **[os]**
- `src/app/wm_compare/graphical_backend_equality.spl:4` -> `os.compositor.tolerance_profile` **[os]**
- `src/app/wm_compare/html_compat_geometry_probe.spl:7` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/html_compat_geometry_probe_24_cli.spl:5` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/html_compat_geometry_probe_cli.spl:4` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/html_compat_geometry_probe_cli.spl:5` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/app/wm_compare/html_compat_geometry_probe_cli.spl:6` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_compare/live_capture.spl:26` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/live_capture.spl:27` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/main.spl:21` -> `std.cli.log_modes` **[tooling-cli]**
- `src/app/wm_compare/native_file_read_smoke.spl:1` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_compare/production_gui_web_renderer_parity.spl:18` -> `std.nogc_sync_mut.env.platform` **[env]**
- `src/app/wm_compare/production_gui_web_renderer_parity.spl:19` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:26` -> `os.desktop.taskbar_shell` **[os]**
- `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:32` -> `std.nogc_sync_mut.env.platform` **[env]**
- `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:33` -> `std.nogc_sync_mut.io.time_ops` **[timer]**
- `src/app/wm_compare/scene_registry.spl:12` -> `os.compositor.wm_scene` **[os]**
- `src/app/wm_compare/simple_html_capture_worker.spl:1` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/simple_html_capture_worker.spl:2` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/simple_html_capture_worker.spl:3` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_compare/site_corpus_compat.spl:3` -> `std.nogc_sync_mut.sffi.io` **[ffi]**
- `src/app/wm_compare/site_corpus_compat.spl:22` -> `app.io.mod` **[io]**
- `src/app/wm_compare/site_corpus_compat.spl:23` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/app/wm_compare/site_corpus_compat.spl:24` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_compare/site_corpus_div_geometry_summary_cli.spl:2` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/site_corpus_div_geometry_summary_cli.spl:3` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_compare/site_corpus_layout_report.spl:3` -> `std.cli.cli_util` **[tooling-cli]**
- `src/app/wm_compare/site_corpus_layout_report.spl:19` -> `std.nogc_sync_mut.io.file_ops` **[io]**
- `src/app/wm_showcase/capture_artifact.spl:10` -> `std.io_runtime` **[io-runtime]**
- `src/app/wm_showcase/session.spl:21` -> `os.compositor.host_compositor_entry` **[os]**
- `src/app/wm_showcase/session.spl:22` -> `os.compositor.simple_web_window_renderer` **[os]**
- `src/lib/common/ui/window_scene_draw_ir.spl:58` -> `os.compositor.display_backend_core` **[os]**
- `src/lib/common/ui/wm_full_stack_demo.spl:19` -> `common.io.window_event` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/backend_screenshot_capture.spl:5` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_compute_evidence.spl:4` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_compute_evidence.spl:5` -> `std.process` **[process]**
- `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl:4` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl:5` -> `std.process` **[process]**
- `src/lib/gc_async_mut/gpu/browser_engine/glass_comparison_runner.spl:6` -> `os.compositor.screenshot_compare` **[os]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/dns.spl:14` -> `std.io_runtime` **[io-runtime]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/dns.spl:15` -> `std.nogc_sync_mut.io.browser_net_runtime` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/fetch.spl:31` -> `std.io_runtime` **[io-runtime]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:21` -> `std.nogc_sync_mut.io.browser_net_runtime` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/tls.spl:15` -> `std.nogc_sync_mut.io.browser_net_runtime` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/security/cookie_policy.spl:31` -> `std.gc_async_mut.http.types` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_file_renderer.spl:2` -> `std.io_runtime` **[io-runtime]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl:10` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl:11` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:3` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:3` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl:11` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl:17` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles_gpu.spl:20` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:37` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:38` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_script_renderer.spl:6` -> `std.io_runtime` **[io-runtime]**
- `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl:21` -> `std.nogc_sync_mut.io.env_ops` **[io]**
- `src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl:22` -> `std.process` **[process]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl:34` -> `std.gc_async_mut.env.platform` **[env]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_intel.spl:36` -> `std.gc_async_mut.io.oneapi_ffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_intel_kernels.spl:9` -> `std.gc_async_mut.io.oneapi_ffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:19` -> `std.gc_async_mut.env.platform` **[env]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:20` -> `std.env.variables` **[env]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:21` -> `std.gc_async_mut.io.metal_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal_font.spl:10` -> `std.gc_async_mut.io.metal_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal_helpers.spl:11` -> `std.nogc_sync_mut.io.metal_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_opengl.spl:36` -> `std.gc_async_mut.io.opengl_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_rocm_runtime_ops.spl:2` -> `std.gc_async_mut.io.rocm_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl:155` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl:12` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_glsl.spl:27` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:10` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:7` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:64` -> `std.gc_async_mut.io.mod_stub` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl:12` -> `std.env.variables` **[env]**
- `src/lib/gc_async_mut/gpu/engine2d/metal_session.spl:16` -> `std.nogc_sync_mut.io.metal_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl:40` -> `std.gc_async_mut.io.vulkan_sffi` **[io]**
- `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl:44` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/web_wm_session.spl:10` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/wm_frame_pacing.spl:11` -> `std.gc_async_mut.io.time_ops` **[timer]**
- `src/lib/nogc_sync_mut/play/wm/mod.spl:28` -> `std.nogc_sync_mut.io_runtime` **[io-runtime]**
- `src/os/services/wm/wm_codec.spl:6` -> `os.userlib.syscall_raw` **[syscall-raw]**
- `src/os/services/wm/wm_codec.spl:7` -> `os.kernel.log.klog_api` **[syscall-raw]**
- `src/os/services/wm/wm_service.spl:31` -> `os.userlib.syscall_raw` **[syscall-raw]**
- `src/os/services/wm/wm_service.spl:33` -> `os.services.launcher.launcher` **[os]**
- `src/os/services/wm/wm_world.spl:6` -> `os.kernel.log.klog_api` **[syscall-raw]**

### C violations — `extern fn` declarations (49)

- `src/lib/gc_async_mut/gpu/browser_engine/browser_file_ops.spl:2` `rt_file_write_text` **[fs]**
- `src/lib/gc_async_mut/gpu/browser_engine/browser_file_ops.spl:3` `rt_file_read_text` **[fs]**
- `src/lib/gc_async_mut/gpu/browser_engine/browser_file_ops.spl:4` `rt_file_read_bytes` **[fs]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/cache.spl:16` `rt_time_now_unix_micros` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:23` `rt_io_tcp_connect_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:24` `rt_io_tcp_read` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:25` `rt_io_tcp_write_text` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:26` `rt_io_tcp_flush` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:27` `rt_io_tcp_close` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:28` `rt_io_tcp_set_nodelay` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:29` `rt_io_tcp_set_read_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl:30` `rt_io_tcp_set_write_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:30` `rt_io_tcp_connect_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:31` `rt_io_tcp_read` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:32` `rt_io_tcp_write_text` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:33` `rt_io_tcp_flush` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:34` `rt_io_tcp_close` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:35` `rt_io_tcp_set_nodelay` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:36` `rt_io_tcp_set_read_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/websocket_client.spl:37` `rt_io_tcp_set_write_timeout` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/ws_crypto.spl:9` `rt_random_hex` **[entropy]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/ws_handshake.spl:19` `rt_io_tcp_read` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/ws_handshake.spl:20` `rt_io_tcp_write_text` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/ws_handshake.spl:21` `rt_io_tcp_flush` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/net/ws_handshake.spl:22` `rt_io_tcp_close` **[net]**
- `src/lib/gc_async_mut/gpu/browser_engine/script/js_compat.spl:48` `rt_random_random` **[entropy]**
- `src/lib/gc_async_mut/gpu/browser_engine/script/js_compat.spl:49` `rt_time_now_unix_millis` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/script/timer_api.spl:19` `rt_time_now_unix_micros` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:4` `rt_time_now_micros` **[timer]**
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:23` `rt_time_now_micros` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:42` `spl_dlopen` **[dynamic-link]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:43` `spl_dlsym` **[dynamic-link]**
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:44` `spl_wffi_call_i64` **[dynamic-link]**
- `src/lib/gc_async_mut/gpu/engine2d/cpu_session.spl:18` `rt_simd_has_sse` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/cpu_session.spl:19` `rt_simd_has_avx2` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/cpu_session.spl:20` `rt_simd_has_neon` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/cpu_session.spl:21` `rt_simd_has_rvv` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/host_ops.spl:2` `rt_cpu_arch_name` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/host_ops.spl:3` `rt_sleep_nanos` **[timer]**
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl:29` `rt_target_arch_name` **[host-capability]**
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_x86_session.spl:30` `rt_target_pointer_bits` **[host-capability]**
- `src/lib/nogc_async_mut/wm/wm_optimization.spl:8` `rt_time_now_micros` **[timer]**
- `src/lib/nogc_sync_mut/play/wm/mod.spl:37` `rt_process_run_timeout` **[process]**
- `src/lib/nogc_sync_mut/play/wm/mod.spl:38` `rt_env_get` **[env]**
- `src/lib/nogc_sync_mut/play/wm/mod.spl:39` `rt_file_exists` **[fs]**
- `src/os/services/wm/wm_codec.spl:61` `mmio_read8` **[mmio/kernel]**
- `src/os/services/wm/wm_codec.spl:62` `mmio_read16` **[mmio/kernel]**
- `src/os/services/wm/wm_codec.spl:63` `mmio_read32` **[mmio/kernel]**
- `src/os/services/wm/wm_codec.spl:64` `mmio_read64` **[mmio/kernel]**

---

## Bucket B — the legitimate host/OS surface (input to the interface lane)

Only **5 edges**, across **3 capabilities**:

- `src/os/services/wm/wm_codec.spl:8` -> `common.window_protocol.window_protocol` [surface+event-protocol]
- `src/os/services/wm/wm_service.spl:30` -> `os.userlib.ipc_protocol` [surface+event-protocol]
- `src/os/services/wm/wm_service.spl:32` -> `common.window_protocol.window_protocol` [surface+event-protocol]
- `src/lib/gc_async_mut/gpu/engine2d/framebuffer_hooks.spl:3` `rt_fb_blit32` [framebuffer-present]
- `src/lib/gc_async_mut/gpu/engine2d/framebuffer_hooks.spl:6` `rt_fb_fill32` [framebuffer-present]

| Capability | Concrete shape today | Interface note |
|---|---|---|
| Window/surface lifecycle | `WmCreateRequest`, `WmResizeRequest`, `WmMoveRequest`, `WmCloseRequest` in `common/window_protocol/window_protocol.spl` | Already a protocol type set — the best existing candidate for the single interface. |
| Input event delivery | `WmInputEvent`, `COMP_INPUT_EVENT`, `WM_INPUT_TEXT_MAX_BYTES` | Same module + `os/userlib/ipc_protocol.spl`. Delivered over IPC, already indirected. |
| 2D presentation | `rt_fb_blit32`, `rt_fb_fill32` (`gpu/engine2d/framebuffer_hooks.spl`) | Raw framebuffer blit. The only direct present path; two externs. |

**Finding for the interface lane:** the surface+event contract is *already* mostly
centralised in `common/window_protocol/window_protocol.spl`. The gap is not that
surface/event calls are scattered — they are not. The gap is that 184 *other* host
dependencies were never held to the same discipline.

### Edges deliberately demoted from B to C by the sharpened test

| Was | Now | Why |
|---|---|---|
| Timers — 22 edges (`std.{gc_async_mut,nogc_sync_mut}.io.time_ops`, `rt_time_now_micros`, `rt_time_now_unix_micros/millis`, `rt_sleep_nanos`) | C | Frame pacing and cache TTLs need a clock, but the WM *runs* without one. A clock is a precondition the contract does not permit. Largest single removable class. |
| CPU-feature / arch probes — 6 (`rt_simd_has_{sse,avx2,neon,rvv}`, `rt_cpu_arch_name`, `rt_target_arch_name`, `rt_target_pointer_bits`) | C | Backend selection, not surface or event. Must have a compile-time or default-safe answer. |
| Clipboard / display enumeration | C | No direct edges found in scope (`common/ui/clipboard_service.spl` is a pure model module); would be C if introduced. |

---

## Per-tier reporting (no collapsing)

Bucket counts by tier of the *importing* file. `use:` = import edges, `ext:` = extern decls.

```
app ext:R 4
app use:A 20
app use:C 80
app use:I 106
common ext:R 6
common use:? 3
common use:A 33
common use:C 2
common use:I 180
gc_async_mut ext:A 53
gc_async_mut ext:B 2
gc_async_mut ext:C 41
gc_async_mut ext:R 43
gc_async_mut use:? 5
gc_async_mut use:A 123
gc_async_mut use:C 47
gc_async_mut use:I 640
gc_async_mut use:R 2
nogc_async_mut ext:C 1
nogc_sync_mut ext:C 3
nogc_sync_mut use:A 2
nogc_sync_mut use:C 1
os ext:C 4
os ext:R 2
os use:B 3
os use:C 5
os use:E 10
os use:I 4
os use:R 1
```

### The four `play/wm` tier copies are not four copies of one thing

| Tier | File | Lines | Externs | Verdict |
|---|---|---|---|---|
| `gc_sync_mut` | `play/wm/*.spl` | 3 | 0 | stub |
| `gc_async_mut` | `play/wm/*.spl` | 7 | 0 | stub |
| `nogc_async_mut` | `play/wm/*.spl` | 11 | 0 | stub |
| `nogc_sync_mut` | `play/wm/*.spl` | **426** | **3** | **the only real implementation** |

The single substantive tier (`nogc_sync_mut/play/wm`) carries 3 of the audit's most
contract-hostile externs: `rt_process_run_timeout`, `rt_env_get`, `rt_file_exists`
(plus `std.nogc_sync_mut.io_runtime.time_now_unix_micros`). It shells out to an external
process. Reporting these four tiers as one module would have hidden that entirely: three
of the four are empty and would have read as clean.

### Cross-tier duplication in the wider surface

CROSS-TIER duplicate module basenames in {gpu/engine2d,gpu/browser_engine,wm,play/wm,ui}:
total dup names=68  divergent bodies=68  identical=0

**68 module basenames exist in 2-3 tiers under `gpu/engine2d`, `gpu/browser_engine`,
`wm`, `play/wm`, `ui` — and all 68 have divergent bodies. Zero are identical.** Chiefly
`gc_sync_mut` vs `gc_async_mut` copies of the engine2d backends
(`backend_cuda`, `backend_metal`, `backend_opengl`, `backend_rocm`, `backend_intel`, …)
and the browser WebGPU/WebGL stack. A fix applied to one tier's copy is **not** applied
to the others. Any enforcement rule must run per-tier.

Note also that `gc_async_mut/gpu/engine2d` imports `std.nogc_sync_mut.gpu.engine2d.sffi_vulkan`
directly — cross-tier reach-through inside the rendering lane itself.

---

## Import weight

In this repo **importing one symbol registers the whole module.** So each C row above is
not "one function" — it is a whole module's worth of host coupling. Concretely:

- `use std.nogc_sync_mut.io.time_ops.{time_now_nanos}` pulls in the entire io.time_ops
  module, not one clock read.
- `use os.userlib.ipc_protocol.{COMP_CREATE_WINDOW}` registers the full IPC constant
  set and whatever that module transitively pulls.
- The 41 `io` + 13 `io-runtime` edges therefore represent far more host surface than 54
  call sites would suggest.

Edge counts in this document are **lower bounds on coupling**, never upper bounds.

---

## What this method CANNOT see

Stated plainly, because a clean report that cannot be defended is worse than a noisy one.

1. **Static, first-order only.** Edges are `use` statements and `extern fn` declarations
   in the 454 in-scope files. **Transitive** dependencies are not followed: if an
   in-scope file imports a clean-looking module that itself opens a socket, this audit
   scores it clean. The true violation count is **higher**, possibly much higher.
2. **Declaration, not call.** An `extern fn` is counted where declared. A declared-but-
   never-called extern is over-counted; an extern declared in one file and called from
   another is counted once. Call-site counts were not built.
3. **No dead-code analysis.** A violation on an unreachable path scores the same as one
   on the hot path. Some of the `wm_compare` harness edges are likely never reached in a
   shipped WM.
4. **Classification is by name, and names lie.** Buckets come from module-path segments
   and symbol prefixes, hand-audited but not proven. `std.common.crypto.sha256` was
   reclassified A (pure hashing) by inspection; a similar misjudgement elsewhere is
   possible. Category `os` (28 edges) is the least precise — it is a catch-all for
   `os.*`/`std.os.*` paths not otherwise resolved.
5. **Module resolution is approximate.** A hand-written resolver maps module paths to
   files; it left **4 of 463** distinct modules unresolved. Those 4 are listed below and
   may be genuinely dangling (recall: in this repo **an unresolved `use` is only a WARN,
   exit 0** — a dangling import does not fail the build, so it can persist unnoticed).
6. **The scope boundary is a judgement.** Scope = the 11 directories named in the brief
   plus everything they import. WM/GUI code living outside those roots is unaudited.
7. **Runtime/JIT/interpreter divergence is invisible.** Source text only. Nothing here
   was executed, so engine-specific behaviour is out of frame.
8. **Docstring false positives were bounded, not eliminated.** 3 prose lines beginning
   `use ` inside `"""` blocks matched the import pattern (~0.2% of 1,270); all 3 were
   identified and excluded. Prose that *coincidentally* matched a real module path would
   not have been caught.

### Unresolved / possibly dangling import targets

```
DANGLING use targets (unresolved): 4 of 463 distinct modules
  src/app/wm_compare/backend_measurement_capture.spl:5  compiler.backend.gpu_portable_compute  [C/compiler]
  src/app/wm_compare/production_gui_web_renderer_parity.spl:8  app.ui.render.html_widgets  [A/render]
  src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:27  app.ui.render.html_widgets  [A/render]
  src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:28  app.ui.web.html  [A/render]
  src/app/wm_showcase/session.spl:32  app.ui.render.html_widgets  [A/render]
  src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl:13  app.ui.web.html  [A/render]
  src/lib/gc_async_mut/gpu/browser_engine/glass_pipeline_compare.spl:14  app.ui.render.html_widgets  [A/render]
  src/lib/gc_async_mut/gpu/browser_engine/style/transform.spl:5  examples.browser.shared.matrix4.Matrix4  [?/unclassified]
```

`app.ui.render.html_widgets` did not resolve from two `wm_compare` files, and
`compiler.backend.gpu_portable_compute` from one. `examples.browser.shared.matrix4` and
`examples.browser.feature.style.computed` are imported by
`gpu/browser_engine/style/{transform,animation_controller}.spl`, but **no `examples/browser/`
tree exists in the repo** — the rendering lane holds imports into a deleted tree.

---

## Method

- Edge list built by script from source: `^\s*use <path>` and `^\s*@?extern(...)? fn <name>`,
  over `.spl` files in the 11 scope roots.
- Counting `grep` pinned to `/usr/bin/grep` (`ugrep` is the default `grep` here); all
  patterns line-anchored.
- Excluded: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`,
  `src/runtime/{miniaudio,stb_image,stb_truetype}.h`.
- Per-tier counts kept separate throughout; no cross-tier collapsing.
- Cross-tier divergence measured by SHA-1 of full file bodies.

## Not done here (owned by sibling lanes)

- No code was changed. Audit only.
- The single host/OS interface set is a **sibling lane**; this document's Bucket B table
  is its input.
- The enforcement rule (lint/CI gate preventing new C edges) is a **third lane**; the
  Bucket C list is its baseline. Note that any such gate must be per-tier — see the 68
  divergent duplicates.
