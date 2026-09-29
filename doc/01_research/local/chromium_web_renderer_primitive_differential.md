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

## Implementation evidence (2026-09-08)

The canonical Simple-side ABI records and fail-closed admission seam now live in
`src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl`. They enforce the
exact five-symbol ABI, absolute test-only library path, bounded request/response,
manifest identity, bridge identity/revision, and strict device-readback receipt.
The focused SFFI contract spec passed 4/4; the converter spec also exited zero.
The former requested compiled mode degraded to interpreter because its harness
contains interpreter-only constructs, so neither result substitutes for a real
native integration test.

The runtime load/call/release functions are now implemented behind the same
SFFI owner. They hash before and after load, resolve the frozen symbol set once,
reject a missing symbol before any call, use bounded caller-owned buffers, map
native statuses, and destroy/close exactly once. Native execution still awaits
the owned bridge dylib. Three macOS shared-library builds failed at
`_worker_loop_entry`; the concrete compiler/linker blocker is tracked in
`doc/08_tracking/bug/pure_simple_macos_shared_library_linker_worker_loop_2026-09-08.md`.
Electron/Chrome semantic evidence remains useful but is inadmissible for GPU
comparison because it reports no device-origin readback receipt.

The native C ABI fixture itself passes. The hosted Simple caller now reaches
load and session creation, but its final integration run fails with
`unsupported-primitive` even though the request contains every required key.
This isolates a managed-byte/raw-pointer projection defect in the bootstrap
interpreter's integer-only dynamic-call path. It is tracked in
`doc/08_tracking/bug/chromium_oracle_simple_caller_byte_pointer_projection_2026-09-08.md`;
the integration attempt reached its three-cycle cap and was not retried.

The corrective implementation replaces that raw request projection with the
runtime's one-call pinned byte-span transport and allocates response plus length
slot as packed byte arrays. This removes boxed-array pointer reinterpretation
from the oracle caller. Focused source checks pass; the fixture gate remains
pending rather than presumed green because the session retry cap still applies.

The real prepared-host broker now verifies exact Electron `42.5.0`, Chrome
`148.0.7778.271`, its own SHA-256, and the exact npm lockfile SHA-256 before
rendering. `package.json` no longer uses a semver range. A live pinned run passed
DOM/style/layout/paint plus trusted pointer, Ctrl+Alt, scroll, and resize input;
its response remains correctly `device_origin_readback=false` with GPU
unavailable. Browser/manifest scalar values now percent-escape separators and a
second live run passed the canonical-scalar check.

### macOS dylib diagnostic (2026-09-08)

A rebuilt bootstrap compiler isolated the shared-library failure to two linker
contracts. Target-aware detection selected the ELF `ld.lld` frontend for a
Mach-O target; it now selects Apple `ld` or fails closed. Darwin SFFI plugins
also need `-undefined dynamic_lookup`, because the loading Simple process owns
the runtime ABI and the plugin must not embed a second runtime instance. Both
focused Rust linker tests pass.

With those corrections, the bootstrap diagnostic build produces a 37,872-byte
arm64 Mach-O dylib. Because that compiler path currently ignores the custom
name in `@export("C", name: ...)`, the bridge's five Simple function identifiers
now equal the frozen ABI names as well. `nm` confirms all five exports. The
artifact is retained only as
`libsimple_chromium_primitive_oracle.bootstrap-diagnostic.dylib`; it is not an
admitted Chrome oracle until a source-matched pure-Simple compiler builds it and
the native load/run/release gate passes. Its diagnostic SHA-256 is
`c7ae2e9e6960bafe9c9fb318cb2553de6a217ee4b13a21d40ffffcda3e967bcf`;
`nm` reports exactly five global `simple_chromium_oracle_*` text symbols.
