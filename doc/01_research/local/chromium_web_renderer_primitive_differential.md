<!-- codex-research -->
# Chromium Web Renderer Primitive Differential — Local Research

## Existing owners to reuse

| Concern | Existing owner | Consequence |
|---|---|---|
| Canonical trace values | `src/lib/common/spec/differential_trace.spl` | Reuse `TraceEvent`/`NormalizedTrace`; native handles, wall time, and mutable buffers remain forbidden. |
| Comparison and profiles | `src/lib/nogc_sync_mut/test/differential_conformance.spl` | Reuse `GpuEnvironmentProfile`, `ReferenceOracleAdapter`, semantic comparison, incomplete-trace rejection, and `chrome-web-oracle` profile. |
| Simple web rendering | `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer*.spl` | Web private semantic/layout state lowers directly to `DrawIrComposition`; it must not become an exported WebIR. |
| Rendering executor | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | Rect/background/border/text/image/path assertions must observe this shared execution route, not a new test painter. |
| Dynamic loading | `src/lib/nogc_sync_mut/sffi/dynamic.spl` | The compiled-only `DynLib`/`spl_dlopen`/`spl_dlsym`/`spl_dlclose` boundary is the only loader owner. |
| Existing Chrome perf scripts | `test/05_perf/web_render_chrome/*` | These contain synthetic records and therefore cannot qualify a primitive differential pass. They remain historical/perf scaffolding only. |

## Findings and constraints

1. `gpu_web_differential_oracle` already reserves a test-only dynamic reference
   owner and requires semantic rather than raw display-list comparison. This
   work extends that capsule.
2. `doc/03_plan/ui/webir_drawir_optimization.md` makes the project decision
   explicit: no nominal `WebIR`/`GuiIR` display-list may be introduced. The
   converter is therefore an adapter into the existing normalized trace, with
   `DrawIrComposition` remaining the Simple terminal display list.
3. Existing Chrome runner and Simple runner both fabricate `source="synthetic"`
   when unavailable. Those artifacts are PENDING only. A dynload adapter must
   return `library-not-found`/`abi-mismatch` etc.; it may never manufacture a
   reference trace or GPU receipt.
4. `std.sffi.dynamic` exposes raw integer pointers and lacks a typed C-string
   return protocol. The bridge ABI must use caller-owned bounded output buffers
   and opaque integer handles rather than leaking native ownership into Simple.
5. A real Chromium component build exports symbols for linking, not a stable
   public renderer ABI. Dlopen of Blink/Viz component internals is therefore
   not supported. A tiny owned C ABI bridge compiled at one pinned Chromium
   revision is the sole reference plugin.

## Primitive boundary selected by the task

The first executable corpus is restricted to: solid rectangle/background,
uniform border, text with font-metric facts, decoded image placement, click and
pointer, keyboard including left/right Ctrl and Alt, scroll, resize, and a
linear path only when both adapters declare it supported. CSS filters, shadows,
transforms, iframes, arbitrary SVG/path, video, WebGL/WebGPU API conformance,
audio, and arbitrary JavaScript are out of scope and must return
`unsupported-primitive`, not a partial comparison.
