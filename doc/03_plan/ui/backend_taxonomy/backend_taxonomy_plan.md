<!-- Generated 2026-06-06 via SPipe agent-team gap analysis (5 agents). Source: workflow wf_a0e34760. -->

# Backend Taxonomy: Plan to Meet Architecture

## 1. Current state vs target

The architecture (`shared_ui_contract.md`, `simple_gui_stack.md`, `ADR-002`) calls for a backend-neutral semantic UI where **shells are peers** (pure-Simple GUI, Electron, Tauri) and **draw lanes** are an orthogonal Engine2D axis (software / cpu_simd / GPU). Today the GUI-shell lane is functionally complete (browser/electron/tauri all run), and the web-render lane is honest and bit-exact against real Chromium. The two GPU lanes are uneven: cpu_simd and metal are real; cuda/opencl are partial; hip/oneapi/webgpu are stub-or-missing. The only live functional blocker is that the pure-Simple GUI window bypasses the compositing-friendly `std.io.window_winit` path, so it won't show live on macOS. Most remaining gaps are doc/wiring; the GPU lanes contain the only large net-new work.

## 2. Status matrix (lane × backend)

| Lane | Backend | Status |
|------|---------|--------|
| GUI Shell | browser (pure_simple) | implemented (macOS live-window blocked) |
| GUI Shell | electron | implemented (S2 by design) |
| GUI Shell | tauri | implemented (S2 by design) |
| web-render | software | implemented |
| web-render | cpu_simd | implemented |
| web-render | metal | implemented |
| web-render | chromium-as-flag | **missing — by design** (peer shell, not a flag) |
| Engine2D 2D | cpu_simd | implemented |
| Engine2D 2D | metal | implemented (macOS only) |
| Engine2D 2D | vulkan | partial (probe hardcoded unavailable in interp) |
| Engine2D 2D | cuda | partial (feature-gated) |
| Engine2D 2D | webgpu | **missing** |
| GPU Process | cuda | implemented (feature-gated) |
| GPU Process | opencl | partial (ICD loads; readback uncertified) |
| GPU Process | hip/rocm | stub (probe hardcoded unavailable) |
| GPU Process | oneapi/sycl | **missing** |

## 3. Phased steps

### P0 — quick wins / unblockers (small wiring)

- **Route pure-Simple GUI window through `std.io.window_winit`.** What: replace facade-bypassing Winit calls in `src/app/ui.browser/app.spl` (event_loop @122, window @127, direct present call @26) with the `WinitLoop`/`WinitWindow` wrapper (`src/lib/nogc_sync_mut/io/window_winit.spl:32-72`: `winit_loop_new`, `winit_window_new`, `winit_present_rgba`, `winit_poll_close_requested`). Why: only the wrapper path composites/AX-enumerates on macOS; raw path never registers with the window server (per macos bug doc Part B caveat). Gate: launch `simple ui browser examples/06_io/ui/web_engine2d_gui.spl` via `scripts/gui/macos-gui-run.shs` and confirm window composites + AX-enumerates (live observation, not a captured fixture).
- **Honest-selection knob audit.** What: confirm shell selection `config.backend` (`HostBackendKind` enum, `shared_wm_stack.md:68`) is actually wired to dispatch; wire it if the enum exists in arch but not in dispatch code. Do **not** invent `SIMPLE_GPU_BACKEND` — GPU-lane selection is parameter-driven by design; state that explicitly. Why: arch mandates a backend-neutral selector; manufactured env knobs are anti-patterns. Gate: `simple ui electron|tauri|browser` each route to the correct shell from the documented selector.
- **Fix ADR-002 doc drift.** What: correct `browser_backend.spl` → `browser_compositor_backend.spl` (`ADR-002` lines 16-18, 47). Why: load-bearing for the decision trail. Gate: file exists at the cited path.
- **Add anti-tautology comment + asserts.** What: in `_normalize_backend_name` (`simple_web_renderer.spl:21-27`) note chromium is a peer shell, not a draw lane; in the bitmap-evidence gate assert `gpu_frame_complete=true AND mismatches=0` on the **GPU readback** side. Why: prevent CPU-mirror false-green. Gate: `scripts/check-electron-simple-web-engine2d-bitmap-evidence.shs`.

### P1 — partial → implemented (medium wiring)

- **Vulkan interpreter dispatch.** What: replace hardcoded "unavailable" in `backend_probe.spl:146-151` with a real native-build availability check (session already exists, `vulkan_session.spl:1-211`). Why: full API surface present but unreachable in the primary test lane. Gate: probe returns Initialized + a compute→readback→pixel cycle (native build).
- **OpenCL readback certification.** What: drive full kernel dispatch → readback → pixel verify in `backend_opencl.spl`; add `submit_us/sync_us/readback_us` timings. Why: ICD loads (`runtime_simd_dispatch.c:108-200`) but readback is unproven. Gate: two-artifact bitmap evidence with absolute oracle, mismatch=0.
- **CUDA build-flag clarity.** What: document/verify `feature="cuda"` in release builds; probe checks link-time availability not just runtime (`cuda_runtime.rs:116`). Why: silent feature-gating. Gate: probe Initialized only when bindings linked.

### P2 — large net-new work (NOT wiring)

- **WebGPU Engine2D session** — net-new `webgpu_session.spl` (device/queue/pipeline) following the Metal/CUDA pattern. Large.
- **HIP/ROCm Tier-1 runtime** — net-new Rust bindings (`hip_runtime.rs`) or dlopen loader for `libamdhip64.so`; replace `gpu_rocm.rs` stubs. Large.
- **oneAPI/SYCL** — currently absent from selection; decide stub-parity (like HIP) vs. Level-Zero dlopen loader. Large.

Gate for all P2: each new backend must clear the same two-artifact honest-comparison protocol below before its matrix status may change from missing/stub.

## 4. Honest-comparison protocol (mandatory)

Every backend-parity claim MUST use **two independently produced artifacts** compared against an **absolute oracle** — never hard-coded captured pixels, never a self-vs-self mirror. False-green history to never repeat: (1) hard-coded Chrome-captured text-raster overlays (`production_gui_web_renderer_parity_hardening.md:74-89`, removed); (2) CPU-mirror equality where MATCH ≠ correct (`engine2d_cpu_metal_bit_parity.md:102-113`, requires `gpu_frame_complete=true`). Passing evidence template: pure-Simple Engine2D vs Chromium (Electron OSR) → `mismatch_count=0`, checksum `26296152649728`, two independently produced artifacts. Trustworthy gates: `scripts/check-simple-web-engine2d-js-bitmap-evidence.shs` (node), `scripts/check-electron-simple-web-engine2d-bitmap-evidence.shs` (real Chromium). Note: the node *layout* reference is a hand-authored mask (matching yourself) — only the Engine2D-vs-Chromium gate is a true cross-implementation oracle.

## 5. Taxonomy (SDN)

```sdn
ui_taxonomy:
  shells (peers):
    - pure_simple: { window: std.io.window_winit, render: Engine2D }   # P0 route fix
    - electron:    { window: BrowserWindow, render: Blink/Chromium }   # S2 by design
    - tauri:       { window: WebviewWindow, render: WebView }          # S2 by design
  draw_lanes (Engine2D, orthogonal):
    cpu:    { scalar: implemented, simd: implemented }
    gpu:
      - metal:   implemented(macos)
      - cuda:    partial(feature-gated)
      - opencl:  partial(readback-uncertified)
      - vulkan:  partial(interp-unavailable)
      - webgpu:  missing            # P2 net-new
      - hip/rocm: stub              # P2 net-new
      - oneapi:  missing            # P2 net-new
  selection:
    shell: config.backend (HostBackendKind)   # P0 verify wiring
    lane:  create_with_backend(name)          # parameter-driven, NOT env (by design)
  invariant: chromium = peer shell, never a draw-lane flag
```
