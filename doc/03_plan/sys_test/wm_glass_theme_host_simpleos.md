# System Test Plan: WM Glass Theme on Host and SimpleOS

## Primary Spec

Executable:
`test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl`

Manual:
`doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md`

## Scenarios

1. Canonical happy path: resolve `aetheric_dark`, assert complete material,
   render host and QEMU through canonical routes, compare semantics and pixels.
2. Interaction: focus swap, pointer drag, maximize/restore, keyboard/text and
   animation frames change semantic and pixel state coherently.
3. CSS matrix: variables, RGBA, gradient, border/radius, layered shadow,
   backdrop blur/saturation, typography and state selectors survive every stage.
4. Accessibility: reduced transparency and unavailable blur choose the named
   solid fallback with readable contrast.
5. Fail closed: corrupt hash, unknown capability, stale capture, legacy QEMU
   entry and forced direct renderer are rejected.
6. Determinism/performance/provenance: hashes and region policies repeat;
   startup/frame/QEMU/RSS metrics and complete identities are retained.
7. Ownership: no fixture, private renderer, raw-runtime or synthetic route.

## Manual Flow

Use these exact visible steps:

1. `Load the Stitch glass theme`
2. `Render the hosted WM through the canonical scene`
3. `Apply glass CSS and widget computed styles`
4. `Boot the canonical SimpleOS desktop in QEMU`
5. `Capture and compare semantic and framebuffer evidence`

Setup helpers are `@inline`; secondary/error/matrix scenarios are folded and
use `@prev` only for already-created evidence. Capture kinds are protocol,
HTML, GUI, binary, log and artifact. The generated manual uses linked evidence.

## Requirement Trace

| Requirement | Scenarios |
|---|---|
| REQ-001 | 1, 5, 6 |
| REQ-002 | 1, 3, 4 |
| REQ-003 | 1, 2, 7 |
| REQ-004 | 1, 3, 7 |
| REQ-005 | 1, 3, 5 |
| REQ-006 | 1, 5, 7 |
| REQ-007 | 1, 5, 7 |
| REQ-008 | 1, 2, 5 |
| REQ-009 | 1, 4, 5 |
| REQ-010 | 1, 5, 7 |
| NFR-001..008 | 1, 4, 5, 6, 7 |

## Focused Regression Specs

### 2026-07-25 admission checkpoint

| Evidence | Admission |
|---|---|
| 16x16 hosted Aetheric capture | Diagnostic only; satisfies no production host, event, or provenance scenario |
| x86 SSE2/static preflight | Pass; QEMU not launched |
| ARM VirtIO/C preflight | Pass; QEMU not launched |
| Aggregate WM glass spec | Fail-fast until exact-current host and QEMU artifacts validate |

### 2026-07-26 CPU-composited material source checkpoint

| Focused source regression | Required claim | Not evidence of |
|---|---|---|
| `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` | WM body retains opaque `DrawIrCommand.color` fallback for native-safe transport while `background-color` carries translucent window material, plus rounded gradient and CPU-composited capability; titlebar remains not-requested | GUI/Web realization, host pixels, QEMU pixels |
| `test/02_integration/rendering/simple_web_css_cascade_spec.spl` | Exact WM opt-in preserves the Aetheric translucent base/backdrop/typed gradient; padded opt-in and unsupported image syntax fail closed | Engine2D execution or host pixels |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` | Draw IR carries opaque fallback plus complete CPU material witnesses; provenance remains none without a matching execution receipt | Native-device execution |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` | Existing Draw IR styled-RECT lowering preserves the opaque fallback when capability is absent and routes a supported request through the canonical material helper | CPU-SIMD or GPU execution |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl` | Rounded corner/center alpha, bounded backdrop blur, gradient endpoints, and saturation arithmetic are pinned as CPU pixel semantics | Vulkan/Metal device readback, events, timing, RSS |
| `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl` | WM provenance admits only exact solid/CPU reason pairs with lowercase SHA-256 formatting | Semantic digest recomputation at the frame boundary |

The source slice is deliberately not a system-spec PASS. The aggregate
`wm_glass_theme_host_simpleos_spec.spl` remains fail-closed until retained,
current-source host and QEMU evidence satisfies the five visible manual steps.
The third source verification cycle had an opaque-material test failure.
Static review corrected the saturation-zero luminance rounding mismatch and
the Web source now preserves the exact Aetheric request, emits complete Draw IR
witnesses, and binds CPU provenance to a successful Engine2D execution receipt.
The session retry cap forbids a post-fix run. Requested blur `30px` is
explicitly realized as blur `4px`, with realized blur/saturation and reduction
witnesses. A fresh pure-Simple PASS is still required before this checkpoint
can be promoted beyond SOURCE PREPARED / UNVERIFIED.

The planned Web repair adds paired evidence:

1. cascaded CSS retains translucent base, two ordered alpha-gradient stops,
   rounded radius, and requested backdrop values;
2. Draw IR carries those semantics plus explicit bounded realization while
   its command color remains the named opaque fallback;
3. advanced Engine2D exact pixels prove backdrop -> base -> gradient ordering;
4. legacy CPU execution proves the same command chooses the opaque fallback;
5. artifact/WM provenance rejects swapping `cpu-composited-material` and
   `solid-material` hashes or kinds.

Extend theme-package, WM-chrome, Simple-Web-window, Web glass-feature-gap,
Engine2D glass, canonical GUI-entry contract and QEMU evidence-contract specs.
Each test uses built-in matchers and concrete values. Missing runtime helpers
must call `fail("wm glass theme evidence not implemented")` until implemented.

### 2026-07-26 no-bootstrap host/backend disposition

| Lane | Current disposition |
|---|---|
| Pure-Simple focused specs | Blocked: generic wrapper fails identity; architecture-specific binary announces the forbidden Rust seed at execution |
| Hosted Aetheric capture | Historical 16x16 local-raster capture only; missing theme-manifest receipt and device path, therefore not admitted |
| CPU/SIMD and Metal | Generic backend checker exists, but it does not bind the current Web/Draw-IR glass material to a device readback |
| Vulkan host events | Generic Web/widget capture scripts exist; current paired Vulkan/Metal glass captures are absent |
| x86_64 QEMU | Static WM/QMP/SSE2 preflight passes; live proof postponed for missing admitted kernel/disk and `grub-mkstandalone` |
| AArch64 QEMU | QEMU/firmware available; live proof postponed for missing admitted kernel/FAT/manifest/frozen-source admission |

No row may be promoted by rebuilding through the Rust seed. W5 resumes only
with an admitted existing runtime/artifact set or on the appropriate host.

### 2026-07-27 cross-host request contract

The executable request contract at
`test/03_system/check/wm_glass_cross_host_evidence_request_spec.spl` keeps the
current macOS lane active and registers fail-closed Windows Vulkan, Linux
Vulkan/RenderDoc, x86 QEMU, and ARM QEMU evidence requests. Its companion
manual is
`doc/06_spec/03_system/check/wm_glass_cross_host_evidence_request_spec.md`.

These tests verify routing and admission requirements only. They do not turn a
postponed external-host row into rendering or event evidence.
