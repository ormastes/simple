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

### Hosted persistent-theme-runtime prerequisite (planned)

This is a design/test-plan handoff only; it creates no executable spec or
runtime PASS yet. The future focused tests use `HostedThemeRuntime` and the
named protocol helper flow
`ready -> theme_init(generation, revision, wire_text) -> theme_ready -> init`:

| Required focused test | Concrete assertion |
|---|---|
| Parent construction ordering | `create_initial(source_reader, registry_path, requested_id)` captures registry once, derives an empty requested ID from those bytes, captures each source once, commits revision `1`, and precedes package/backend/compositor/worker activity; no cached default lookup or module-global/per-handle store is reachable. |
| Hosted callers | Browser, Electron, Tauri, TUI, and TUI-Web reuse one app-owned runtime through `HostedWmSession`/`init_host_wm_with_runtime`; the headless WM daemon remains explicitly excluded. |
| Initial worker envelope | Worker rejects HTML/frame before exact `theme_init(generation, revision, wire_text)`; `theme_ready` echoes generation/revision plus derived identity/hashes before first HTML/frame. |
| Apply envelope | Exact `theme_apply(generation, expected_predecessor_revision, revision, wire_text)` rejects wrong generation, stale predecessor, skip/coalescing, duplicate revision, and unknown version; changed revisions are consecutive and `theme_ready` echoes all envelope scalars plus derived identity/hashes. |
| Wire isolation/bound | Canonical immutable `text` contains no revision. An accepted canonical encoding must satisfy codec-owned public byte length `<= THEME_PACKAGE_INSTALL_WIRE_V1_MAX_UTF8_BYTES`; decoder and protocol reject public byte length `MAX + 1`. Success is required at the greatest constructible valid codec fixture, and at exact `MAX` only if the codec fixture proves that a valid canonical encoding of exactly `MAX` is constructible. Public reads expose one copied `(revision, wire_text)` or derived scalars, never aggregate/map aliases or duplicate current fields; feature-local/direct `rt_*` conversion is absent. |
| Transaction publication | Counting/changing reader proves one canonical read per path; competing/stale/max-revision and explicit unchanged no-op prove one locked `(revision, wire_text)` old-or-new payload and no notification/write on failure/no-op. |
| Parent admission | Refresh fails before swap while any WM/GUI/Web consumer uses sequential globals; migrated consumers observe one store revision before `ThemeChangedV1`. |
| Frame identity | Browser frame protocol and `WmContentFrame` carry explicit `theme_revision` and `theme_material_sha256`; mismatches are rejected and `content_revision` remains independently unchanged. |
| Restart fence | Replacement worker receives current envelope first and initializes only from an explicit parent-owned replay payload; absent replay, old generation/revision frame, or hash mismatch leaves `web-frame-unavailable`. |

These tests must be introduced as real source/unit or protocol specs with
concrete assertions and fail-fast placeholders where implementation is absent.
They must not use a bootstrap seed, package-file reads in a worker, a synthetic
frame as a current-revision receipt, or a hand-edited generated manual. The
aggregate WM glass system spec remains fail-closed until these protocol tests
and current-source host/QEMU evidence are accepted.

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
| `test/01_unit/os/compositor/wm_aetheric_web_material_spec.spl` | Production Aetheric WM request resolves package surface `0xCC1F1F21`, `blur(30px) saturate(170%)`, one typed CPU-composited Draw IR witness, and a matching Engine2D software execution receipt | Admitted pure-Simple execution, native Metal/Vulkan/SIMD, host/QEMU capture |
| `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` | A final device readback after CPU glass stays CPU; missing/mismatched dispatch stays none; only exact Metal operation receipt promotes device material | Live Metal dispatch and framebuffer parity |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` | Software glass records `cpu-scalar-glass-v1` and zero Metal count/handle/identity | Native Metal operation |
| `test/02_integration/rendering/metal_msl_pipeline_spec.spl` | Optional snapshot/material pipelines and completed device operation produce device readback with no pending command ownership; outside/corner/center samples over a translucent backdrop must exactly match the CPU scalar oracle | Admitted pure-Simple execution plus host screenshot/event/timing evidence |

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

The 2026-07-27 current-host adapter repair restored the exact material mode
that had been removed from the production WM wrapper and resolved committed
conflict text in `simple_web_window_renderer_spec.spl`. The new focused
adapter-to-Draw-IR spec was attempted twice with the deployed macOS
interpreter; both runs timed out at 120 seconds during setup/source work
before an assertion executed. These are not semantic failures, but they are
also not PASS evidence; no retry or bootstrap is authorized for this session.

The Metal source lane adds a stronger, independent operation receipt. A valid
device result requires the exact Metal glass target, matching producer/device
counts, zero CPU executions, positive device framebuffer handle and identity,
and a final device readback. The final readback cannot promote CPU glass by
itself. Its shared source-over helper uses the same straight-alpha
destination weighting and output unpremultiplication as the CPU oracle, and
the live spec samples device parity over a translucent backdrop. The embedded
MSL compiles with the installed macOS Metal compiler, but the live integration
spec has not run on an admitted pure-Simple runtime and therefore remains
SOURCE PREPARED / RUNTIME UNVERIFIED.

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

### 2026-07-30 GUI/Web/2D design checks

| Layer | Focused source evidence | Rejected false claim |
|---|---|---|
| Web cascade | 2/3/4-value corners, authored shorthand/longhand order, exact Aetheric outer+inset parse, transparent alpha, malformed color and integer overflow rejection | Device or pixel realization |
| Web Draw IR | Complete ordered `web-box-shadow-layers-v1` indexed fields; valid `none` emits count `0`; malformed omits schema; legacy keys unchanged | Partial typed admission |
| Engine2D | Independently admitted zero-shadow four-corner clip, shadow-without-corner ordering, inset edge without center corruption, bounded malformed/legacy fallback | Corner-exact outer silhouette/nonuniform border, GPU/device execution |
| GUI/WM architecture | Producers use common Draw IR only and do not import Web parsing or Engine2D raster internals | Parallel GUI renderer |

The focused source checks remain unverified until a current admitted
pure-Simple runtime can execute them. Live GUI/Web captures, event handling,
CPU-SIMD, Metal/Vulkan readback, and x86/ARM QEMU evidence remain separate
rows.

Focused unit owners:

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_box_effects_spec.spl`

### 2026-07-30 hosted event/presentation source gate

`test/01_unit/os/desktop/hosted_wm_evidence_spec.spl` must prove that only an
accepted, newer semantic event replaces the current receipt and that the next
monotonic host presentation records completion time, input-to-present latency,
present count, and skipped-frame count. Invalid semantic callbacks and
regressive presentation counters/timestamps must leave the accepted receipt
unchanged. This source gate repairs the live
`src/os/hosted/hosted_entry.spl` import/call boundary; it does not substitute
for a current native host event/capture run or delegated QEMU evidence.
