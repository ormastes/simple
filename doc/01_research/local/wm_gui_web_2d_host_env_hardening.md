<!-- codex-research -->
# WM/GUI/Web/2D Host Environment Hardening — Local Research

## Finding

The production hosted route already exists: winit events enter
`HostCompositor`, Simple Web supplies window pixels, the compositor builds one
`DrawIrComposition`, and persistent Engine2D submits and reads back the frame.
The smallest hardening change should reuse this route and its existing live
gates, not add a second driver or renderer.

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.local_research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.local_research hash=sha256:auto render=ascii
@layout dag
@direction LR

HostScreen -> HostedEntry
HostedEntry -> HostCompositor
HostCompositor -> SimpleWebContent
HostCompositor -> SharedWmScene
SharedWmScene -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> BackendReadback
HostCompositor -x GuiWebSemanticDispatch
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.local_research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Existing Production Owners

| Area | Existing owner | Evidence/gap |
|---|---|---|
| Host input | `src/os/hosted/hosted_entry.spl:363-478` | Real winit pointer, button, wheel, key, focus, and presentation loop |
| WM lifecycle | `src/os/compositor/host_compositor_core.spl:984-1063,1375-1453` | Hit-test/focus/drag/damage; no semantic content dispatch |
| Web content | `src/os/compositor/simple_web_window_renderer.spl:207-251` | Authoritative HTML to cached pixel artifact; recovery fallback is marked |
| WM Draw IR | `src/lib/common/ui/window_scene_draw_ir.spl:976-998` | Canonical scene composition; nested content Draw IR is still fail-closed |
| Engine2D execution | `src/os/compositor/compositor_engine2d.spl:53-90` | Persistent backend execution |
| Event targeting | `src/lib/common/ui/draw_ir.spl:478-560` | Reusable target context, currently not called by hosted input |
| GUI producer | `src/lib/common/ui/widget_draw_ir.spl:272-304` | Canonical widget-tree conversion, separate from hosted WM content route |
| SIMD detection | `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:34-142` | SSE4.2/AVX2/AVX512/NEON/RVV levels and cached live probe |
| Backend probe | `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl:107-156` | Maps SIMD availability by architecture |
| Host test env | `src/lib/nogc_sync_mut/spec/env_detect.spl:13-282` | OS/arch/GPU/AVX2/NEON only; lacks RVV, Vulkan, RenderDoc, input, readback |
| Vulkan readback | `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:744-767` | Distinguishes device readback from fallback/cache |
| RenderDoc | `src/app/test/renderdoc_runtime_ops.spl:1-45` | Existing availability and Vulkan device wrapper |
| Coverage | `src/lib/nogc_sync_mut/coverage.spl:1-204` | Branch counts require both true and false outcomes |

## Strongest Existing Tests

- `test/03_system/gui/linux_hosted_wm_live_window_spec.spl:272-325` retains real
  X11/xdotool input, render revisions, PNG, framebuffer PPM, and correlation,
  but ordinary SSpec runs only its self-test and retained evidence.
- `test/03_system/os/wm/arm64_simpleos_qmp_input_spec.spl:14-73` runs QMP input,
  RAMFB capture, before/after hashes, damage, and guest revision checks.
- `test/02_integration/rendering/metal_engine2d_readback_spec.spl:104-224`
  proves a positive handle and `device_readback`; the CPU mirror is parity only.
- `test/02_integration/rendering/vulkan_strict_spec.spl:92-211` is the reusable
  live-or-unavailable Vulkan contract.

## Confirmed Gaps

1. No `TestHostEnv`/`test_host_env` aggregate exists.
2. Hosted OS input changes WM state but does not dispatch into GUI/Web semantic
   targets; `draw_ir_event_target_context` has no hosted caller.
3. No single portable scenario correlates real input, target dispatch, state
   mutation, canonical composition, and same-frame device readback.
4. WebGPU readback at
   `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl:543-557` is a CPU
   mirror and cannot satisfy device evidence.
5. `HostCpuConfig` and compiler target inference omit live RVV coverage; the
   existing SIMD spec also omits RVV from accepted levels.
6. No current coverage report proves 98% of the owned aggregate contract.

## Reuse Decision

Reuse the existing probes, production owners, live gates, and coverage engine.
Add only the missing aggregate/receipt seam and the smallest production event
bridge required by the selected requirements.
