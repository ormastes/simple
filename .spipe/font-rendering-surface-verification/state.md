# Feature: Font Rendering Surface Verification

## Raw Request
$sp_dev font rendered on simple gui/web/2d and wm on host properly check add
modern sspec tests for them to check. and font rendering on wm on simple os on
qemu verification and add tests for it. when 2d backend of simple 2d is simd
and vulkan. do thing is pherallel 1. 2d, 2. web 3. gui 4. host wm 5. simple os
wm. device tasks for agents and assign sol model for 4 and 5 lane. fully verify
font rendering draw event handling of wm/gui/web/2d impl

## Task Type
feature

## Refined Goal
Prove and, where necessary, repair production font drawing and correlated input
event delivery through the canonical Simple 2D, Web, GUI, hosted WM, and
SimpleOS QEMU WM paths, including honest SIMD and Vulkan backend evidence.

## Acceptance Criteria
- AC-1: A modern SSpec drives the public Engine2D facade with the pinned font
  through both requested `cpu_simd` and `vulkan` lanes, asserts semantic text
  input, absolute glyph-region pixels, exact CPU-oracle parity, and honest
  backend/readback provenance; unavailable Vulkan is reported as unavailable,
  never PASS.
- AC-2: A modern SSpec proves production HTML/WebIR emits the selected text and
  ordered advances into the exact submitted `DrawIrComposition`, produces
  nonblank readable glyph evidence, and correlates focus, keyboard, pointer,
  timing, and animation events with that frame.
- AC-3: A modern SSpec proves `widget_tree_to_draw_ir` emits the selected text,
  style, bounds, and event/source metadata into the exact submitted
  `DrawIrComposition`, produces nonblank readable glyph evidence, and delivers
  focus, keyboard, and pointer events to the visible widget.
- AC-4: A live host SSpec/evidence gate proves
  `SharedWmScene -> DrawIrComposition -> Engine2D` renders pinned-font glyphs
  in the production hosted WM and correlates focus, move/maximize/restore,
  keyboard, pointer, WM state, frame generation, and framebuffer readback.
- AC-5: A fail-closed QEMU SSpec/evidence gate boots the canonical SimpleOS
  `gui_entry_desktop.spl`, proves the exact pinned font guest path/length/hash,
  observes guest glyph/frame markers, captures an independent QMP `pmemsave`
  glyph crop, and correlates injected keyboard/pointer/window events with IRQ,
  WM state, and frame generation.
- AC-6: Every executable scenario lives under `test/`, uses `std.spec.*`,
  user-observable `it` names, imperative `step("...")` calls, direct matchers,
  absolute oracles, deliberate-red calibration where a wrapper determines the
  verdict, and no placeholder or boolean-wrapper assertions.
- AC-7: Mirrored `doc/06_spec/**/*.md` manuals expose the primary flow and
  captures without opening source and report zero stubs. The shared font flow
  uses these exact primary phrases: `Load the pinned multilingual font
  manifest`; `Accept exact-face-bound simple-script shaping`; `Prepare one
  shared font batch for 2D and 3D`; `Emit the selected font composite program
  and plan compilation`; `Prove native submission and device readback`.
- AC-8: Production paths reuse `FontRenderer`, transient `FontRenderBatch`,
  common atlas ownership, `DrawIrComposition`, and Engine2D `draw_text`; no
  private GUI/Web/WM font renderer, atlas, cache, backend poke, or Engine3D
  shortcut is introduced.
- AC-9: Focused specs and runnable mirrors pass once on the pure-Simple
  self-hosted binary; required GUI sanity apps and applicable SIMD/Vulkan,
  hosted-window, event-routing, and QEMU wrappers produce retained evidence
  with exact commands and artifact paths.
- AC-10: Architecture, test plan, agent-task plan, generated manuals, UI/font
  guides, SPipe process references, LLM wiki links, feature tracking, and any
  changed wrapper documentation are current; `doc/06_spec` contains zero
  executable `_spec.spl` files and both direct-runtime guards pass.
- AC-11: A highest-capability reviewer audits each lane against AC-1..AC-10,
  rejects synthetic/same-path/CPU-mirror evidence, and final verification
  reports PASS only when every required current-host and QEMU row has
  authoritative evidence.
- AC-12: A separate RV64 QEMU dev-board gate boots the canonical
  `riscv64/gui_entry_desktop.spl`, proves the exact pinned guest font
  path/length/hash and an RV64-only glyph crop, rejects an independently
  one-byte-corrupted crop, and correlates QMP VirtIO keyboard and pointer
  delivery with guest IRQ, WM state, and later frame generations. x86_64
  evidence cannot satisfy this row.
- AC-13: Each of the six production routes has a source-to-test boundary row
  naming its producer, canonical consumer, identity carried across the link,
  visible outcome, negative disconnection/replay case, and authoritative
  executable/manual evidence. Source-contract assertions may guard wiring but
  cannot replace the runtime pixel/event assertions in AC-1..AC-5 and AC-12.

## Scope Exclusions
- Engine3D HUD/world text and non-Linux native host backends are out of scope.
- A Vulkan-unavailable host remains visible as unavailable and blocks the
  Vulkan acceptance row; it is not silently replaced by software.

## Cooperative Review
- Parallel lanes: 2D, Web, GUI, hosted WM, x86 SimpleOS QEMU WM, and RV64
  SimpleOS QEMU WM.
- Merge owner: `/root`.
- Final reviewer: highest-capability `/root` review after lane integration.
- Hosted WM and SimpleOS QEMU WM use `gpt-5.6-sol` agents as requested.
- Shared production interfaces to reuse: `DrawIrComposition`, `FontRenderer`,
  `FontRenderBatch`, `Engine2D.create_requested_backend`,
  `widget_tree_to_draw_ir`, `SharedWmScene`, and
  `HostCompositor.render_frame_engine2d`.
- Manual flow helpers: the five exact shared-font phrases in AC-7, plus
  `Build the production surface composition`, `Submit the exact composition`,
  `Deliver correlated focus keyboard and pointer events`, and
  `Capture backend and framebuffer evidence`.
- Setup/checker helpers: reuse existing surface facade setup, canonical
  production renderer parity/event wrappers, hosted WM live-window/capture
  wrappers, and SimpleOS fullscreen QMP wrapper. Do not add a second runner.
- Any temporary helper must call `fail(...)` or `assert(false)` until backed by
  real semantic, event, and readback evidence.
- Generated-manual review owner: `/root`; lane agents generate and self-review
  their focused manual before handoff.

## Runtime Boundary Decision
- runtime_need: none established.
- facade_checked: existing UI, Web, Engine2D, text-layout, hosted compositor,
  QEMU runner, env, process, and file facades.
- chosen_path: reuse-facade.
- rejected_shortcuts: raw `rt_*` aliases, fixture-only painters, direct backend
  field access, synthetic handles, CPU mirrors labeled as GPU, private font
  paths, and serial-only QEMU claims.

## Module Boundary Coverage — 2026-07-24

| Route | Producer -> consumer | Carried identity | Positive oracle | Negative oracle | Evidence/status |
|---|---|---|---|---|---|
| 2D | `DrawIrText -> Engine2D.draw_text -> FontRenderer -> backend` | face, advances, composition, backend/readback | exact direct/DrawIR CPU parity plus requested SIMD/Vulkan rows | inconsistent advance count/width rejects before rendering | modern SSpec/manual; live run BLOCKED |
| Web | `HTML -> WebIR -> DrawIrComposition -> Engine2D` | run ID, composition ID, face, pixel-artifact checksum, frame correlation | readable ARGB glyph artifact and focus/key/pointer/timing frame | stale ID rejects before Electron; only one same-ID invocation can claim final PASS | modern SSpec/manual; receipt creation BLOCKED |
| GUI | `WidgetTree -> widget_tree_to_draw_ir -> Engine2D` | composition ID, scene key, target/source | visible `Ready -> ReadyZ` pixels and correlated input | replayed scene key remains unresolved | modern SSpec/manual; live window BLOCKED |
| hosted WM | `SharedWmScene -> HostCompositor -> Engine2D` evidence route | command nonce, phase, revision, checksum | pinned glyph crop and focus/move/maximize/restore frames; compatibility fallback cannot qualify | non-increasing nonce is ignored and exact ACK identity is required | modern SSpec/manual; live hash/runtime BLOCKED |
| x86 QEMU | `gui_entry_desktop -> WM -> Engine2D -> QMP` | guest font hash, input sequence, WM/frame generation | independent `pmemsave` glyph crop and correlated events | QMP disconnect, replay, corrupt crop, demo markers reject | modern SSpec/manual; current image build BLOCKED |
| RV64 QEMU | `riscv64/gui_entry_desktop -> WM -> VirtIO/QMP` target route (font/input currently unwired) | RV64 font hash, IRQ/input sequence, WM/frame generation | RV64-only bottom-right glyph crop and input ordering | unavailable markers, corrupt crop, stale/out-of-order input reject | modern SSpec/manual; font/input wiring BLOCKED |

## Phase
dev-done

## Log
- dev: Created state file with 11 acceptance criteria (type: feature).

## Research Summary

### Existing Code
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl:467-620` owns requested CPU,
  SIMD, and Vulkan construction plus the canonical text executor.
- `src/lib/common/ui/widget_draw_ir.spl:244-265` owns GUI widget-to-Draw-IR.
- `src/os/hosted/hosted_entry.spl:209-424` owns live hosted canonical frames
  and input dispatch.
- `scripts/check/check-simpleos-wm-fullscreen-evidence.shs:305-962` owns the
  canonical desktop QEMU font crop and correlated input oracle.
- Existing selected requirements, architecture, design, and test plan live in
  the `shared_multilingual_gpu_fonts` artifacts; this campaign closes their
  unresolved production-surface rows instead of creating a second design.

### Reusable Modules
- `FontRenderer`, `FontRenderBatch`, `DrawIrComposition`,
  `widget_tree_to_draw_ir`, `HostCompositor.render_frame_engine2d`, and the two
  existing hosted/QEMU evidence wrappers provide every required owner surface.

### Domain Notes
- Vulkan is locally executable on two NVIDIA devices; QEMU, Xvfb, xdotool, and
  `spirv-val` are installed. `glslangValidator` is unavailable.

### Open Questions
- NONE

<!-- sdn-diagram:id=font-rendering-surface-verification.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font-rendering-surface-verification.research hash=sha256:auto render=ascii
@layout dag
@direction LR

WebIR -> DrawIrComposition
WidgetTree -> DrawIrComposition
SharedWmScene -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> FontRenderer
Engine2D -> CpuSimd
Engine2D -> Vulkan
SimpleOSQemu -> SharedWmScene
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font-rendering-surface-verification.research hash=sha256:auto
WebIR -----\
WidgetTree ---> DrawIrComposition -> Engine2D -> FontRenderer -> CPU SIMD/Vulkan
WM Scene ---/                                ^
SimpleOS QEMU -------------------------------/
```

</details>
<!-- sdn-diagram:end -->

## Requirements
- REQ-1 (AC-1): Honest public Engine2D font pixels and provenance for
  `cpu_simd` and Vulkan — area: `src/lib/gc_async_mut/gpu/engine2d/`.
- REQ-2 (AC-2): Production WebIR text plus correlated browser events — area:
  `src/lib/common/ui/` and `test/03_system/app/simple_web/`.
- REQ-3 (AC-3): Production widget Draw IR text plus correlated widget events —
  area: `src/lib/common/ui/` and `test/03_system/app/simple_gui/`.
- REQ-4 (AC-4): Live hosted canonical WM glyph and event evidence — area:
  `src/os/hosted/` and `test/03_system/gui/`.
- REQ-5 (AC-5): Canonical SimpleOS QEMU font hash/crop and input correlation —
  area: `examples/09_embedded/simple_os/` and `scripts/check/`.
- REQ-6 (AC-6..AC-11): Modern manuals, canonical ownership, fresh docs, and
  independent highest-capability review — area: `test/`, `doc/`, `.spipe/`.
- REQ-7 (AC-12): Separate canonical RV64 QEMU font crop and VirtIO input
  correlation — area: `examples/09_embedded/simple_os/arch/riscv64/`,
  `scripts/check/check-rv64-display-smoke-qmp-evidence.shs`, and
  `test/03_system/os/wm/`.

## Architecture

### Module Plan
| Module | Path | Role | Change |
|---|---|---|---|
| Engine2D | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | requested backend and canonical text execution | only if constructor invariant is broken |
| GUI Draw IR | `src/lib/common/ui/widget_draw_ir.spl` | preserve widget text/style/event metadata | only if focused spec reproduces a gap |
| Hosted desktop | `src/os/hosted/hosted_entry.spl` | canonical live frame and event correlation | only if focused gate lacks production receipts |
| SimpleOS desktop | canonical x86 compositor/shell entry files | guest pointer/keyboard/frame correlation | only if QEMU reproduces missing receipts |
| Evidence | existing wrappers plus six focused specs/manuals | fail-closed semantic, event, and pixel oracles | modified/new |

### Dependency Map
- WebIR, widget tree, and `SharedWmScene` depend on `DrawIrComposition`.
- Engine2D consumes Draw IR and transient `FontRenderer` material.
- Hosted and SimpleOS platform code presents final pixels and input only.
- No producer depends on a backend; no circular dependencies are introduced.

### Decisions
- **D-1:** Reuse the existing production owners and wrappers because parallel
  renderers or test-only painters would weaken the claim.
- **D-2:** Pair semantic/event receipts with an absolute glyph crop because
  either source inspection or pixel equality alone can false-green.
- **D-3:** Keep unavailable device rungs failed/unavailable because CPU mirrors
  are not Vulkan or QEMU proof.

### Public API
- No new public production API is planned.
- Existing `Engine2D.create_requested_backend`,
  `widget_tree_to_draw_ir`, and `HostCompositor.render_frame_engine2d` remain
  the surface contract.

### Requirement Coverage
- REQ-1 -> Engine2D and 2D SSpec.
- REQ-2 -> WebIR producer and Web SSpec.
- REQ-3 -> widget producer and GUI SSpec.
- REQ-4 -> hosted desktop wrapper/SSpec.
- REQ-5 -> SimpleOS compositor/QEMU wrapper/SSpec.
- REQ-6 -> manuals, plans, guides, guards, and final review.
- REQ-7 -> RV64 entry/QMP wrapper/SSpec and retained guest font/input/frame evidence.

<!-- sdn-diagram:id=font-rendering-surface-verification.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font-rendering-surface-verification.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

Producers -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> FontRenderer
Engine2D -> CpuSimd
Engine2D -> Vulkan
HostedPlatform -> FinalPixels
SimpleOSPlatform -> FinalPixels
Events -> Producers
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font-rendering-surface-verification.arch hash=sha256:auto
Events -> Producers -> Draw IR -> Engine2D -> FontRenderer -> CPU SIMD/Vulkan
                                         \-> hosted/SimpleOS final pixels
```

</details>
<!-- sdn-diagram:end -->

## Phase
arch-done

## Log
- research: Reused six canonical owners and the selected shared-font artifacts;
  no external research gap remains.
- arch: Preserved one acyclic Draw-IR-to-Engine2D font path with six focused
  evidence lanes and no new public production API.

## Specs

### Spec Files
- `test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl`
  — SIMD/Vulkan semantic, pixel, oracle, and provenance row.
- `test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl`
  — exact WebIR composition plus live browser events.
- `test/03_system/gui/feature/gui_font_event_surface_spec.spl` — exact widget
  composition plus pointer/focus/key delivery.
- `test/03_system/gui/linux_hosted_wm_live_window_spec.spl` — production hosted
  frame/glyph/event evidence.
- `test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl`
  and `test/03_system/check/simpleos_wm_fullscreen_evidence_simple_bin_spec.spl`
  — guest font and pointer correlation contract.
- `test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl` — separate RV64
  guest font/crop and VirtIO input/frame evidence contract.

### Generated Manuals
- `doc/06_spec/03_system/gui/linux_hosted_wm_live_window_spec.md` — generated,
  zero stubs.
- Truthful manual mirrors now exist for 2D, GUI, and SimpleOS system evidence;
  each records BLOCKED/FAIL and cannot be promoted without a qualifying run.
- The Web manual now exists and truthfully records BLOCKED. Its wrapper requires
  a production-Simple composition receipt and pixel artifact before Electron
  starts; earlier self-stamped DOM evidence is quarantined as rejected.
  Pure-Simple docgen remains unavailable.

### AC Coverage Matrix
| AC | Lane | Current status |
|---|---|---|
| AC-1 | 2D | blocked before examples; no Vulkan readback |
| AC-2 | Web | BLOCKED: authoritative receipt is joined by run ID/checksum and atomically limited to one final PASS; execution remains unavailable |
| AC-3 | GUI | source/spec/artifact contract present; execution blocked |
| AC-4 | hosted WM | source/spec/manual present; native artifact/crop blocked |
| AC-5 | SimpleOS WM | source/spec present; build stopped before QEMU/crop |
| AC-6 | test quality | PASS: focused contracts are fail-closed/static-quality clean |
| AC-7 | retained capture | FAIL: authoritative production captures incomplete |
| AC-8 | ownership | PASS: canonical Draw IR/Engine2D ownership preserved |
| AC-9 | backend proof | FAIL: no qualifying SIMD/Vulkan execution |
| AC-10 | release hygiene | FAIL: required manuals/execution incomplete |
| AC-11 | final review | PASS: highest review completed and withheld overall PASS |
| AC-12 | RV64 SimpleOS WM | BLOCKED: font asset is not mounted, VirtIO input is not consumed, and no genuine RV64 crop hash is pinned |
| AC-13 | module links | static boundary matrix and modern negative cases present; live link coverage remains BLOCKED with the owning runtime rows |

## Implementation
- The attempted `Engine2D._from_backend(RenderBackend, ...)` constructor
  consolidation was removed after it proved to erase the concrete trait
  receiver and cause the nil-receiver regression. Engine2D constructors are
  restored to their concrete baseline paths.
- `src/lib/common/ui/widget_draw_ir.spl` preserves GUI source metadata and the
  visible input ID.
- `src/os/hosted/hosted_entry.spl` fails closed instead of accepting a
  compatibility frame during live evidence.
- Hosted move events now dirty the compositor so the existing live gate can
  require a later frame revision instead of waiting on an impossible update.
- `src/os/compositor/compositor.spl` preserves PS/2 AUX bytes for the pointer
  decoder; `src/os/desktop/shell.spl` emits correlated pointer IRQ/state/frame
  receipts.
- The SimpleOS workflow preserves one running QEMU admission job across newer
  pushes; its existing workflow contract locks that policy.
- Web and GUI focused specs/manuals use the shared exact-composition and
  correlated-input step names.
- No new font renderer, atlas, cache, raw runtime alias, or public API was added.

## Verification Progress
- DIAGNOSTIC ONLY: live Chromium/Electron focus, keyboard, text input, pointer down/up,
  positive timing, two animation frames, CSS animation, and zero tolerance;
  the correlated `WEB` frame is a retained 29x20 BGRA artifact whose size,
  checksum, and 273 non-background pixels are independently revalidated at
  `build/test-artifacts/simple-web-font-frame-correlation/`. Highest review
  rejected it as AC-2 proof because raw HTML self-stamps the identity and no
  authoritative checksum joins it to the production DrawIrComposition.
- PASS (static contract only): the Web wrapper and independent validator now
  reject a missing/mismatched production-Simple composition receipt or ARGB
  artifact; the current live row is therefore BLOCKED rather than promoted.
- PASS: hosted wrapper shell syntax, focused diff check, zero-stub hosted manual,
  and working/staged direct-runtime guards.
- DIAGNOSTIC ONLY: one release-path smoke constructs CPU Engine2D, clears it,
  and reads four exact pixels, but its own log identifies the executable as
  Rust-built bootstrap material. It is retained at
  `build/test-artifacts/engine2d_cpu_constructor_clear_smoke/` and does not
  qualify as pure-Simple, font, SIMD, or Vulkan evidence.
- BLOCKED: 2D/Web/GUI pure-Simple SSpecs fail before examples with
  `field access on nil receiver` in the self-hosted Engine2D path. A proposed
  argv0 change was rejected and removed because it would delegate to the Rust
  seed; it is not valid pure-Simple evidence. Root cause was the newly added
  concrete-backend-to-trait constructor helper; that helper is now removed,
  but no qualifying pure-Simple executable is available and the capped focused
  specifications have not been rerun.
- BLOCKED: the focused GUI spec now passes the pure-Simple static check, but its
  first executable `bin/release/simple test` attempt exited 139 before any
  example or retained capture. The new UISession identity boundary is therefore
  source-validated only; no GUI pixel or event PASS is claimed.
- The GUI identity boundary is now wired through BrowserApp/BrowserBackend:
  the exact stamped composition is rendered and host input is dispatched
  through the session envelope. Static app checks pass; runtime admission still
  awaits a non-crashing pure-Simple execution.
- The current rebased `bin/release/simple` also exits 139 during the Web focused
  `check` before loading examples, so Web remains source/contract-only in this
  lane; no browser pixels or event receipt are promoted.
- Bounded provenance diagnosis identifies that exit 139 as a stale deployed
  pure-Simple CLI, not a Web/GUI/font source failure: the binary is the known
  `rt_env_set` ABI-mismatch artifact from
  `doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`.
  A fresh Stage2–4 self-hosted rebuild is required before focused checks can
  run against current source.
- RV64 source audit remains blocked below the shared renderer: the display ABI,
  guest font media, VirtIO input transport, and guest-addressed `pmemsave`
  metadata are absent. The RV64 manual and tracker retain those gaps without
  pinning an x86 crop or claiming serial-only evidence.
- BLOCKED: a cache-preserving full-driver bootstrap attempt ran for 600 seconds
  with one CPU-bound worker, produced no output or cache progress, and exited
  124. The observation is appended to
  `doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`;
  no stage-2 self-build was possible.
- BLOCKED: the hosted native build ran about 10 minutes at 99.6% CPU and
  approximately 2.9 GiB RSS with zero cache objects and no artifact. The
  missing post-move dirty transition is fixed, but remains unclaimed until the
  live gate runs on a qualifying pure-Simple binary.
- BLOCKED: the SimpleOS native build ran about 13 minutes, exceeded
  `--timeout 300`, retained 1,325 cache files, emitted no refreshed kernel, and
  never launched QEMU. CI cancellation policy is fixed, but no protected run
  has completed yet.
- Correctly unclaimed: hosted glyph pin, SimpleOS crop/hash, Vulkan
  device-origin readback, executed GUI font pixels, qualifying generated
  manual provenance, full verification, commit, and sync.
- BLOCKED: the distinct RV64 WM/font/input contract is source-ready in
  `--wm-font-input` mode, but the canonical entry truthfully reports missing
  guest font mounting and VirtIO input consumption. No current-source RV64 ELF
  or RV64-only crop hash was available, so no build or QEMU run was attempted.

## Phase
implement-active

## Log
- spec: Added six modern surface rows. Hosted has a generated manual; 2D,
  Web, GUI, x86 SimpleOS, and RV64 SimpleOS have truthful manual mirrors that remain BLOCKED
  pending qualifying pure-Simple docgen/execution.
- implement: Removed the trait-erasing constructor regression and rejected the
  seed-delegating CLI workaround. Runtime evidence remains blocked by the lack
  of a qualifying self-hosted binary and nonconvergent native builds.
- design: Added AC-12/REQ-7, a distinct RV64 SSpec/manual, and a fail-closed
  extension of the existing RV64 QMP wrapper. Static/self-test evidence only;
  live RV64 font and input proof remains blocked and unclaimed.
- review-fix: RV64 PASS now requires the exact guest font identity/route marker
  and rejects every font/input unavailable marker before crop or input
  acceptance. The live SSpec invokes the real fail-closed wrapper and contains
  no unconditional placeholder failure.
- review-fix: Replaced the x86 fullscreen spec's unconditional placeholder
  helpers with one invocation of the existing fail-closed QEMU wrapper. A
  successful run must validate the retained font/input bundle; an unavailable
  runtime remains explicit non-PASS. No QEMU run was performed in this repair.
- review-fix: The x86 live scenario now checks nonzero scanout metadata, exact
  capture size, retained hashes, and monotonic keyboard/restore/pointer
  sequences. It no longer claims the separate drag/minimize/taskbar or 30-pair
  performance requirements, whose focused scenarios remain blocked.
