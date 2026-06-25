# Backend Taxonomy Plan — TL;DR

Make the impl match the architecture: **shells are peers** (pure-Simple / Electron /
Tauri), **draw lanes are an orthogonal Engine2D axis**. GUI-shell lane is functionally
complete; web-render is honest & bit-exact vs real Chromium (mismatch=0). Only live
blocker: pure-Simple GUI window bypasses `std.io.window_winit` → won't composite on macOS.
GPU lanes uneven: cpu_simd/metal real; cuda/opencl partial; vulkan partial; hip/webgpu/oneapi missing.

**Key invariant:** `chromium` is a peer **shell**, never a web-renderer draw-lane flag.

P0 (wiring): route browser window through `std.io.window_winit`; verify shell-selection
knob; fix ADR-002 path drift; add anti-tautology asserts. P1: vulkan interp dispatch,
opencl readback cert, cuda build-flag clarity. P2 (large net-new): webgpu/hip/oneapi.

Honest-comparison protocol: two independently produced artifacts + absolute oracle,
never memorized pixels (false-green history: Chrome-captured overlays; CPU-mirror equality).

```sdn
ui_taxonomy:
  shells (peers): [ pure_simple(winit+Engine2D), electron(Chromium), tauri(WebView) ]
  draw_lanes (Engine2D, orthogonal):
    cpu: [scalar:done, simd:done]
    gpu: [metal:done, cuda:partial, opencl:partial, vulkan:partial, webgpu:miss, hip:stub, oneapi:miss]
  selection: { shell: config.backend, lane: create_with_backend(name) }  # lane param-driven, not env
  invariant: chromium == peer shell, never a draw-lane flag
```

Full plan: [backend_taxonomy_plan.md](backend_taxonomy_plan.md)
