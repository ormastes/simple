<!-- codex-design -->
# Parallel Implementation Plan — Rendering IR and Full HTML/CSS

Date: 2026-07-29
Status: proposed; feature direction selected, NFR target pending

## Shared target

```
HTML/CSS semantic state ─┐
GUI/UI retained state ───┤
Simple 2D / WM ──────────┼─> DrawIrComposition
graphical TUI / CLI ─────┘       |
                                 v
                               UiIr
                                 |
              Vulkan / CUDA / HIP / Metal / DirectX / CPU
```

`DrawIrComposition` is the stable semantic display list. `UiIr` is its compact,
Vulkan-optimized-first execution form. HTML/CSS never imports GPU backends;
GPU executors never parse HTML/CSS or own layout.

## Frozen interfaces

Existing interfaces retained:

- `simple_web_layout_render_html_draw_ir(...) -> DrawIrComposition`
- `widget_tree_to_draw_ir(...) -> DrawIrComposition`
- `shared_wm_scene_draw_ir_composition(...) -> DrawIrComposition`
- `DrawIrSourceInfo`
- `draw_ir_diff_compositions(...)`
- `draw_ir_patch_between(...)`

New Lane 1 interfaces:

- `UiIr`
- `UiIrLimits`
- `draw_ir_to_ui_ir(composition, limits) -> Result<UiIr, text>`
- `ui_ir_validate(ui_ir, limits) -> Result<bool, text>`
- `ui_ir_execute_cpu(ui_ir) -> UiIrExecutionResult`
- `ui_ir_execute_vulkan(ui_ir, session) -> UiIrExecutionResult`

CUDA/HIP, Metal, and DirectX use the same execution-result contract. Exact
backend function names remain provisional until existing backend session
signatures are reviewed.

Frozen SSpec helpers:

- `expect_document_tree`
- `expect_computed_style`
- `expect_layout_box`
- `expect_draw`
- `expect_ui_ir`
- `expect_rendered_pixels`
- `expect_reference_match`

Any helper added before implementation must call `fail(...)`.

## Ownership rule

| Area | Lane 1: Rendering IR | Lane 2: HTML/CSS |
|---|---|---|
| `src/lib/common/ui/draw_ir*.spl` | exclusive | read-only |
| new `src/lib/common/ui/ui_ir*.spl` | exclusive | read-only |
| Engine2D and GPU backend files | exclusive | forbidden |
| widget/WM/TUI/CLI Draw IR adapters | exclusive | read-only |
| browser HTML parser, DOM, CSS, style, layout | read-only | exclusive |
| browser Draw IR producer implementation | interface review only | exclusive |
| IR unit/system specs | exclusive | may consume public helpers |
| HTML/CSS/WPT SSpec and manifests | read-only | exclusive |
| shared architecture/requirements docs | merge owner | append-only proposals |

Neither lane edits a file owned by the other. Lane 2 records a missing Draw IR
capability in the capability queue below; Lane 1 implements the shared command
only after confirming GUI/2D semantics and compatibility.

## Lane 1 — Rendering IR refactoring and GPU execution

### R1. Baseline and command matrix

Scope:

- Inventory every Draw IR command/style/resource/clip/embedding path.
- Record legacy pixel, event-target, serialization, diff/patch, and backend
  behavior for representative 2D, GUI, WM, Web, text, image, and animation
  scenes.
- Record Vulkan upload bytes, draw/dispatch count, p50/p95, max RSS, fallback
  count, device identity, and readback checksum.

Exit:

- Every production render path has an owner and fixture.
- Same-input Draw IR and pixels are deterministic.
- No backend is credited through a synthetic handle or CPU mirror.

Estimate: 1–2 weeks.

### R2. UiIr contract and validator

Scope:

- Add fixed-width, indexed `UiIr`, pass, primitive, clip, transform, resource,
  payload, dirty-region, and evidence records.
- Begin with Vulkan-friendly 16-byte alignment and bounded side tables.
- Keep text/nested arrays/options out of the hot primitive buffer.
- Reject overflow, invalid ranges, cycles, stale resource generations,
  unsupported kinds, and nondeterministic ordering before allocation.
- Preserve stable command identity, scene revision, order, clips, resources,
  and explicit fallback policy from Draw IR.

Exit:

- Rect/text/image/clip fixtures lower deterministically.
- Malformed and over-budget inputs fail before backend state changes.
- SDN/Draw IR compatibility remains unchanged.

Estimate: 2–3 weeks.

### R3. CPU oracle and incremental lowering

Scope:

- Reuse existing Engine2D CPU/SIMD primitives as the UiIr correctness oracle.
- Lower Draw IR patches/resource generations without rebuilding unchanged
  payloads.
- Cache only by scene, Draw IR revision, backend capability, viewport/DPI, and
  resource revision.
- Add counters for lowered/reused commands, bytes, resources, and dirty regions.

Exit:

- Full and incremental UiIr produce exact identical pixels.
- A small retained update cost scales with changed commands, not scene size.
- No second raster algorithm is introduced.

Estimate: 2–4 weeks.

### R4. Vulkan-first executor

Scope:

- Pack UiIr into bounded staging/storage buffers.
- Group commands only inside explicit pass/order barriers.
- Use existing Vulkan session, pipelines, resource lifetime, present, and
  device-readback owners.
- Support rect, image, text/glyph, clip, path, transform, group/composition,
  opacity/blend, and dirty-region families incrementally.
- Unsupported work is explicit mixed fallback, never silent success.

Exit:

- 2D, GUI, Web, text, image, clip, and animation fixtures match the CPU oracle.
- Evidence proves device execution, final ownership, readback, and presentation.
- Measured warm performance improves or records a concrete blocker.

Estimate: 4–8 weeks.

### R5. CUDA/HIP, Metal, and DirectX parity

Scope:

- CUDA and HIP/ROCm execute coarse compute batches into device framebuffers;
  algorithms remain shared and generated artifacts remain backend-specific.
- Metal maps UiIr passes to render/compute encoders.
- DirectX maps UiIr passes to D3D command lists.
- Presentation/interoperability remains platform-owned.
- All backends declare accelerated command families and honest fallback counts.

Exit per backend:

- Native pipeline/kernel execution is proven independently of counters.
- Exact deterministic pixels match the CPU oracle.
- Upload, dispatch/draw, fallback, present, readback, p50/p95, and RSS evidence
  is retained.
- Hardware absence is reported as blocked, never passed.

Estimate: 2–5 weeks per backend, overlapping where hosts are available.

### R6. Producer cutover and legacy deletion

Scope:

- Route Simple 2D, GUI/UI, WM, Web, graphical TUI, and graphical CLI through
  Draw IR to UiIr.
- Dual-run each legacy path until semantic, pixel, input, animation, and
  performance parity passes.
- Delete only proven duplicate render logic; retain explicit compatibility
  adapters where external APIs require them.

Exit:

- One Draw IR/UiIr execution path serves every graphical producer.
- No duplicated font, image, clip, diff, cache, or backend renderer remains.

Estimate: 3–6 weeks.

## Lane 2 — Full HTML and CSS support

### W1. Standards manifest and modern SSpec foundation

Scope:

- Pin WHATWG HTML, CSS module/snapshot, and WPT revisions.
- Replace tag/property counts with behavior rows: parser, DOM, cascade,
  computed/used values, layout, paint, events, animation, and accessibility.
- Map every row to requirement, spec section, WPT/reftest, implementation owner,
  executable SSpec, and status.
- Modernize existing specs only where evidence is missing: canonical matchers,
  `step("...")`, REQ traceability, typed HTML capture, Draw IR/pixel assertions.

Exit:

- No inventory-only row claims rendering support.
- Unsupported behavior is explicit.
- Generated manuals contain primary flows and zero stubs.

Estimate: 2–4 weeks.

### W2. WHATWG parser, tree construction, DOM, and UA defaults

Scope:

- Tokenization states, tree-construction modes, insertion modes, foster
  parenting, adoption agency, entities, templates, foreign content, quirks,
  and error recovery.
- Element semantics, replaced-element classification, form state, document
  metadata, and default user-agent styles.
- Keep parser/DOM structures private to Web; emit Draw IR only after style and
  layout.

Exit:

- Pinned tokenizer/tree-construction suites meet the selected threshold.
- Error recovery and DOM trees match expected structures.
- Every rendered HTML element has behavioral rather than presence-only evidence.

Estimate: 8–16 weeks.

### W3. CSS syntax, cascade, selectors, values, and queries

Scope:

- Tokenization/parsing, declaration validity, origins, importance, layers,
  inheritance, custom properties, computed/used values, units, math/functions,
  selectors/pseudo classes/elements, media/container/supports queries.
- Reject a declaration containing unsupported components rather than partially
  applying it.
- Use compact indexed rule/declaration data; no repeated full stylesheet scans
  during matching or animation.

Exit:

- Cascade/selector/value WPT groups meet selected thresholds.
- Computed-style fixtures cover happy, edge, invalid, inherited, and dynamic
  cases.
- Representative style recalculation is bounded by affected rules/nodes.

Estimate: 12–24 weeks.

### W4. Layout and typography

Scope:

- Normal/inline flow, whitespace, line boxes, floats/clear, positioning,
  stacking contexts, tables, flexbox, grid, multicolumn, fragmentation,
  containment, writing modes, BiDi, shaping, and replaced-element sizing.
- Resolve geometry and glyph advances before Draw IR.
- Preserve one layout result for paint, hit testing, accessibility, and script
  geometry queries.

Exit:

- Layout WPT/reftest categories meet selected thresholds.
- Layout boxes, line fragments, hit targets, accessibility bounds, and Draw IR
  agree.
- No paint-only geometry workaround exists.

Estimate: 20–40 weeks.

### W5. Paint, compositing, scrolling, and animation

Scope:

- Backgrounds, borders, generated content, lists, images/forms, shadows,
  gradients, transforms, opacity, blend, filters, masks, clips, overflow,
  scrolling/sticky, transitions, animations, and post-load mutation.
- Emit only shared Draw IR capabilities. Missing capabilities enter the queue
  for Lane 1; Web never calls GPU backends.
- Keep animation style/layout/paint invalidation incremental and bounded.

Exit:

- Semantic style/layout/Draw IR assertions precede pixel/reftest evidence.
- Selected animation frames, transitions, scroll, and dynamic mutations match
  expected pixels without resetting time.
- No CSS feature passes from parser state alone.

Estimate: 16–32 weeks; overlaps W3/W4 by feature slice.

### W6. Full conformance closure

Scope:

- Run the pinned local WPT/reftest manifest by module and dependency.
- Classify every failure as parser, cascade, layout, paint, font/raster,
  interaction, harness, or unsupported.
- Require exact Simple internal parity; use explicit cross-browser tolerance
  only for controlled font/antialiasing differences.
- Remove stale inventory/status gates after behavioral replacements pass.

Exit:

- The selected pinned HTML/CSS conformance manifest has no unexplained failures
  and no unsupported required row.
- Corpus, security, animation, memory, and performance gates remain green.

Estimate: multi-quarter; depends on selected conformance threshold.

## Cross-lane capability queue

Lane 2 may request only semantic drawing needs:

| Need | Required description | Lane 1 response |
|---|---|---|
| command family | CSS/HTML behavior and resolved geometry/paint semantics | shared Draw IR + UiIr representation or explicit rejection |
| resource | immutable payload, generation, dimensions, format, lifetime event | stable resource id/range; backend handles stay private |
| composition | stacking/pass boundary, clip, opacity/blend requirement | shared ordering/pass semantics |
| evidence | expected Draw IR and exact/tolerant pixel regions | CPU oracle plus available GPU readbacks |

The queue entry must include a minimal HTML/CSS fixture, expected semantic
output, reference pixels, spec section, and unsupported fallback. Lane 1 owns
the contract edit; Lane 2 owns the Web producer and conformance case.

## Parallel milestones

| Milestone | Lane 1 | Lane 2 | Merge gate |
|---|---|---|---|
| M0 | R1 baseline/matrix | W1 manifest/SSpec inventory | frozen interfaces and fixture IDs |
| M1 | R2 UiIr rect/text/image/clip | W2 parser/DOM slices | HTML fixture reaches valid Draw IR and UiIr |
| M2 | R3 incremental CPU oracle | W3 cascade/selectors/values | dynamic style update changes only expected commands |
| M3 | R4 Vulkan executor | W4 layout slices | CPU/Vulkan pixels and layout agree |
| M4 | R5 GPU parity | W5 paint/animation slices | backend matrix reports honest full/mixed frames |
| M5 | R6 producer cutover | W6 conformance closure | legacy deletion plus pinned manifest pass |

## Merge and review

- Lane 1 owner: rendering-contract lead.
- Lane 2 owner: Web standards/conformance lead.
- Merge owner: highest-capability Codex/main-thread owner.
- Final reviewer: independent highest-capability reviewer.
- Lower-model sidecars: permitted only for read-only inventory, fixture
  classification, and backend evidence collection; they do not approve shared
  interfaces, conformance exclusions, generated-manual quality, or done marks.
- Integration cadence: merge small vertical slices at M0–M5 gates; never merge
  one multi-month branch.

## Shared stop conditions

- Maximum three verify/fix cycles per slice.
- Do not rerun an unchanged green criterion.
- No full bootstrap; use the smallest sufficient pure-Simple phase.
- A compiler/runtime blocker is recorded and the slice stops.
- No Rust-seed or source-status substitute for executable rendering evidence.

