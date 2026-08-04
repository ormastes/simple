# WebRender GPU Offload Plan (remaining WebScene lanes)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — this
plan indexes its remaining work groups; that document stays authoritative for
contracts, ownership and gates. Parser/style/layout/link/placement halves are
covered by the sibling lane plans in this directory.

## Scope

Everything in the GPU WebScene lane not owned by a sibling plan:

| Group | Content |
|---|---|
| W1 | `@gpu_event` GPU-safe Simple script compiler (HIR effect/bound analysis → GpuEventIR → ProcessingIR → CPU oracle + SPIR-V/CUDA/MSL/DXIL/SIMD) |
| W2 | GPU event core: input ring, coalescing, hit query, capture/target/bubble, deterministic mutation journal, host-effect ring |
| W6A/W6B | GPU image codecs (WebP/PNG staged decoders, libwebp oracle) and video surfaces (Vulkan Video VP9/AV1, zero-copy YUV) |
| W7/W8* | WebScene scheduler + platform adapters (Vulkan/Metal/DX/CUDA/WebGPU tiers 0–2) |
| W9 | Host services + SimpleOS bridge (effect services, IVSHMEM, fault restart) |
| W10/W11 | Web integration (feature flags, shadow → candidate → promotion) + evidence |
| I1–I12 | DrawIR v3 program: contract, capacity/no-realloc pools, typed tables, diff/patch, CPU oracle sinks, count/scan/emit + Prepared2D, hit index, cache, v2/v3 adapters, execution backends, Engine2D integration, evidence |

## Structural-compute bindings (normative)

- WebScene device pools = Object VM arenas (gpu_mmu lane contracts); no
  private placement layer.
- Mutation journal commit = MutationIR snapshot semantics; scene generation is
  a `SnapshotId`.
- DrawIR v3 `SourceProvenanceTable` = MappingGraph edges (`PaintOf`,
  `HitRegionOf`).
- Invalidation frontiers = DirtyMask + selector-feature model shared with the
  html_css_parser lane.
- DrawIR v3 is a packed encoding of the one shared display list
  (`DrawIrComposition` — DrawIR v2); it is not a second display-list format.
  The WebIR rejection stands: `doc/03_plan/ui/webir_drawir_optimization.md`
  §Decision. Table/pool implementations follow ADR-004 write-back semantics
  (`doc/04_architecture/adr/ADR-004-indexed-access-value-semantics.md`).

## Variable execution config

The web renderer supports the full offload spectrum as **configuration**, per
the shared rule (README "Variable execution configuration"):

```text
cpu only       flags off — current CPU path, byte-identical (W10 gate)
compatibility  L0–L3 accepted and reported; L4 = full CPU document render
balanced       shadow/candidate — CPU authoritative or GPU with CPU recovery
full offload   strict GPU profile — L0/L1 only; any L2–L5 fails the test
```

Mode selection is per session via feature flags + `ExecutionProfile`; no
rebuild, no silent downgrade (`cpu_selected` by cost policy ≠ `gpu_fallback`).

## Ownership and ordering

Owned paths, feature flags, waves (WAVE 0–5), dependency graph, and acceptance
gates are defined in the parent plan §10–§14 and are not duplicated here.
Ownership ledger: `doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn`.

Implementation ordering (parent §15): DrawIR v3 foundation (I1–I3) and the
`@gpu_event` compiler + event transaction model (W1/W2) first; full GPU
DOM/style/layout/media stages connect only after the first vertical slice
(panel/button/flex/custom-property fixture on Vulkan) passes its proofs:

```text
no allocator call after startup · no pixel readback · no per-widget submission
CPU oracle state/layout/IR/pixel parity · clean device-loss recovery
flag-off byte-identical to current behavior
```

## Compile-time offloadability check

Staged per `doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md` §D4:

- **Now (zero compiler changes):** transitive scanner
  `src/app/gpu_lint/gpu_runnable_scan.spl` (`bin/simple run` it) inventories
  engine2d + browser_engine roots against the ban list, with the
  any-def-blocked overload-taint rule. **Inventory mode first** — warnings and
  a ratchet on blocked/tainted counts, not build errors.
- **Later (W1 lane):** `@gpu_runnable` semantic pass in `35.semantics` wiring
  `gpu_checker` + the `alloc_inference` fixpoint; only that pass meets the W1
  acceptance bar that every rejection names the exact unsupported construct
  and call chain. The scanner stays as the out-of-band cross-check.
  Process notes: `doc/00_llm_process/feature_expert/gpu_offload_check/skill.md`.

## Test evidence (2026-08-02)

All seven GPU-offload spec lanes are landed and green (re-verified 2026-08-02
on the interpreter-backed `bin/simple test` lane; Results lines verbatim):

| Lane | Spec | Results |
|---|---|---|
| HTML parser GPU (flat projection, CPU-oracle parity) | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` | 24/24 |
| CSS parser GPU tables (style_block_parse + selector) | `.../css_parser_gpu_tables_spec.spl` | 47/47 |
| DOM build GPU offload | `.../dom_build_gpu_offload_spec.spl` | 38/38 |
| CSS apply + transform (decl_apply lane) | `.../css_decl_apply_transform_spec.spl` | 61/61 |
| GPU script load + animation ticks | `.../browser_script_animation_gpu_spec.spl` | 22/22 |
| 2D rendering GPU offload parity (device provenance) | `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl` | 17/17 |
| Full-GPU-offload web showcase + capture verification | `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` | 13/13 |

Supporting gates: engine2d renderer unit spec 23/23, backend resolver spec
6/6 (viable-probe auto-resolution, commit `b0ef8e6aee5`), tile grid + paint
parity 21/21 (commit `f86f4c45354`). Capture evidence in the showcase lane:
deterministic checksum, mutation sensitivity, pixel probes for the pinned
palette, and honest offload provenance (device identity required for any
device-readback claim; `host_cache_after_device_present` carries identity per
the backend_vulkan provenance fix).

**Coverage (2026-08-04).** Measured with `SIMPLE_COVERAGE=1` (test_runner
epilogue injection; commit `1a6c1e362a5`).

> **RETRACTION (defect D, `27f864e35e8`).** An earlier revision of this
> section published the numbers below as measured coverage and stated that
> "every target module now clears the 90% `@cover` target". **That claim was
> false and is withdrawn.** Every figure in the "reported" column was
> inflated by a collector defect that conflated line hits across files, and
> on the four modules measured under identical conditions **three fall below
> 90%**. The honest figures are in the second table.

Previously reported (INFLATED — do not cite):

| module | 2026-08-02 | corrected baseline | reported | claimed ≥90% |
|---|---|---|---|---|
| `selector_matcher.spl` | 97% | 97% | 98% | yes |
| `dom_limits.spl` | 100% | — | 100% | yes |
| `style_block_resolve.spl` | 77% | 77% | 99% | yes |
| `style_block_parse.spl` | 72% | 77% | 96% | yes |
| `html_tokenizer.spl` | 64% | 90% | 98% | yes |
| `html_tree_builder.spl` | 28% | 72% | 95% | yes |
| `dom_identity_index.spl` | 50% | 51% | 98% | yes |

**Honest coverage after the defect-D fix.** Same specs, same binary, fix B
held constant, only the hit key varying. **Every module dropped; none rose.**

| module | reported | honest | ≥90% | comparability |
|---|---|---|---|---|
| `..._paint_tiles_gpu.spl` | 100% | **96%** | yes | exact |
| `style_block_resolve.spl` | 99% | **87%** | no | exact |
| `selector_matcher.spl` | 98% | **87%** | no | exact |
| `style_block_parse.spl` | 96% | **85%** | no | exact |
| `html_tree_builder.spl` | 85% | 79% | no | narrower spec set |
| `html_tokenizer.spl` | 79% | 74% | no | narrower spec set |
| `dom_identity_index.spl` | 63% | 59% | no | narrower spec set |
| `..._engine2d_presenter.spl` | 48% | 35% | no | narrower spec set |
| `dom.spl` | 87% | 62% | no | narrower spec set |

The first four rows reproduced the previously-published figures exactly
(96/99/98/100) under the pre-fix key, which is what establishes that the
instrument matched the original conditions. The remaining rows were measured
against a narrower spec set, so both of their columns sat below the
full-corpus value.

**That full-corpus re-measurement is now done, and it supersedes the table
above.**

## Honest full-corpus coverage (2026-08-04, post-A/B/C/D)

365 specs, selected by transitive import closure. **`floor`** is what the tool
prints; **`ceiling`** adds back lines misfiled under `<entry>` (see defect E).
Re-measured 3× on two renderer specs — byte-identical, so the wall-clock
timing noise reported earlier did not reproduce under these conditions.

| module | floor | ceiling | ≥90% |
|---|---|---|---|
| `selector_matcher.spl` | **100%** (72/72) | 100% | yes |
| `style_block_resolve.spl` | **98%** (311/317) | 99% | yes |
| `html_tokenizer.spl` / `html_tree_builder.spl` | **97%** | 99% | yes |
| `style_block_parse.spl` | **97%** (478/488) | 99% | yes |
| `..._paint_tiles_gpu.spl` | **96%** (64/66) | 100% | yes* |
| `dom_identity_index.spl` | **94%** | 99% | yes |
| `..._paint_tiles.spl` | **93%** | 100% | yes |
| `..._core.spl` | 89% | 92% | no |
| `..._engine2d_presenter.spl` | 87% | 96% | no |
| `..._foundation.spl` | 83% | 87% | no |
| `..._layout.spl` | 80% | 84% | no |
| `..._declarations.spl` | 79% | 91% | no |
| `dom.spl` | 79% | **100%** | no |
| `..._renderer.spl` | 78% | 82% | no |
| `..._decl_apply.spl` | 70% | 76% | no |
| `..._style.spl` | 65% | 72% | no |
| `..._paint_layout.spl` | 64% | 68% | no |
| `..._paint_primitives.spl` | 43% | 51% | no |
| `dom_limits.spl` | **0%** (0/2) | 100% | unmeasurable |

**Seven modules clear 90%** — the original parser and style targets among
them. The earlier "not met" verdict was itself measured against a narrower
spec set and is superseded.

Binary capability was established by **positive probe, not size or banner**:
the deployed `bin/simple` (02:04) and the main repo's `target/release` seed
(12:42) both **lack fixes B and D**, so a rebuild from a pristine worktree at
`origin/main` was mandatory. Probes: `covkey_dead_b` reports **20% (2/10)**
where the defect said 100% (D fixed); a `me bump` body is fully covered while
an uncalled `me` body stays 0 (B fixed); a `pub fn` body is attributed to the
`pub fn` and an `elif` head is absent from a hand-counted denominator of 20
(A/C fixed). The measuring tool reproduces the real runner byte-for-byte
(`80% (16/20)`).

### What cannot reach 90%, and why

- **`dom_limits.spl` — 0% forever.** It has only 2 recordable lines, both
  module-level. Its previously-published "100%" was defect D.
- **`..._paint_tiles_gpu.spl` 96% is dead code** — **zero callers in `src/`**;
  a single spec calls it directly. The percentage is real; the relevance is
  not.
- **`_paint_primitives` 43% / `_paint_layout` 64% / `_style` 65%** —
  385/513, 336/481 and 104/135 uncovered lines sit in functions **never
  called at all** (`fb_background_radial_stack_clip`, `paint_tiled`,
  `parse_background_layers`, `inherit_style`). Partly genuine dead code, and
  partly because **14 specs timed out at 900 s**, including
  `tile_paint_parity_spec` and `simple_web_renderer_spec` — which is exactly
  why `paint_tiled` shows as uncalled.
- **`..._engine2d_presenter` 87%** — the remainder is
  `_sample_web_gpu_paint_choice`, device identity and readback: class (c),
  requiring a real GPU. Not faked.

### Corpus honesty

3,938 examples ran. **50 specs executed 0 examples** (38 of which declare
`it` blocks), 14 timed out, and 197 specs carry 1,576 failing examples —
concentrated in browser_session / webgpu / hosted, largely outside these
modules. A mutation audit on `style_block_parse` found 9 lines RED and
**7 covered-but-not-discriminated**; those 7 are reported, not counted as
coverage.

### Defect E — `<entry>` misfiling is far larger than first bounded

The defect-D lane bounded the residual `<entry>` misfiling at "≤2 lines,
≤0.9% per module". **That bound is wrong.** It swallows whole *method
bodies*: 16 lines / 21 points on `dom.spl`, and **119 lines** on
`..._decl_apply.spl`. Proven on a single-module run, with a mutation test
killing lines the reporter calls uncovered. This under-reports, so it is the
conservative direction — but the floor/ceiling split above exists because of
it, and `dom.spl`'s true figure is 100%, not 79%.

### Defect F — no spec can observe `case Some(...)` at all

The interpreter never `Some`-wraps a bare argument passed to a `T?`
parameter, so `case Some(x)` matches nothing and the `match` falls through
silently. The JIT is correct; specs run interpret-only. Consequence:
**none of 1,762 `case Some(` sites across 423 files is observable by any
spec in this repo.** It also makes `selector_matches` silently degrade
`a > b` into descendant matching.

**Most of the original gap was tooling, not untested code.** Four defects
were found in the coverage tool itself — the first three inflating nothing
(they under-reported), the fourth inflating everything:

- **A (fixed, `9c598987bb7`)** — `_cov_report_for_file` stripped only
  `static `, so `pub fn` bodies were charged to the *previous* declaration and
  read as uncovered. This one fix moved `html_tokenizer.spl` 64% → 90% with
  **zero test changes**, and accounts for 5 of the points on
  `style_block_parse.spl`.
- **C (fixed, same commit)** — `elif` heads counted in the denominator but
  were never recorded even when taken.
- **B (fixed, `c1b350a2f9d`)** — instance methods never entered the
  collector's `functions` section, so a `me` method body scored 0% however
  well tested. `record_function_call` was reached from only three of the
  interpreter's call paths; **five more never recorded**:
  `exec_function_with_values_inner`, `exec_function_with_values_and_self`
  (class/enum method dispatch, 12 call sites),
  `exec_function_with_captured_env` (closures/lambdas, 8 call sites),
  `interpreter_control::exec_method_body` (`with` +
  `call_method_if_exists`), and
  `special::execution::exec_function_with_self_return` (mutating-self
  dispatch). A ninth path, `new` bodies via `class_instantiation.rs`,
  bypasses the shared choke point entirely.

  The fix moves the hook down into `execute_function_body` — the single point
  all eight funnel through — and **deletes the three upstream copies** so
  counts are preserved rather than doubled, plus one hook for `new` bodies.
  The reporter gate was not touched. Effect, measured with two seed binaries
  built from hash-verified-identical `.spl` sources and run serialized:
  `html_tree_builder.spl` 75% → **95%**, `dom_identity_index.spl` 52% →
  **98%**, with `html_tokenizer.spl` as a control (97% → 98%) and test
  outcomes byte-identical across both arms.

  This was also the true mechanism behind `dom.spl` measuring 1% despite the
  38/38 DOM lane exercising it heavily — the earlier "under-attribution"
  framing was directionally right but never named the cause. Note the
  post-defect-B figures quoted here (95%, 98%) are themselves inflated by
  defect D; see the retraction above for the honest values.

- **D (fixed, `27f864e35e8`)** — the collector conflated line hits **across
  files**, so an executed line in file A marked the same line number in file
  B as covered whenever B's enclosing function had also been called. Unlike
  A/B/C this defect inflated, and it inflated everything.

  The cause sat deeper than the reporter: `span_to_location` returned the
  literal `"<source>"` as the file for *every* recorded line, so the collector
  pooled all files into one bucket (`total_files: 1` on a multi-file run).
  Keying on `(file, line)` was not merely absent reporter-side — the
  information did not exist. The fix has `span_to_location` read
  `CURRENT_EXEC_MODULE`, a thread-local already saved and restored around
  `execute_function_body`; no new AST field and no new thread-local were
  needed, the plumbing existed and coverage simply wasn't reading it. The
  reporter then keys hits on `(file, line)`, reconciling absolute recorded
  paths against relative `@cover` targets by `/`-anchored suffix match. The
  enclosing-function gate is unchanged.

  Proof by construction: a fixture where file A executes lines 3–11 and file
  B's lines 4–11 never execute (guard always false) while B's enclosing
  function IS called. Honest coverage for B is 2/10 = 20%; the pre-fix
  collector reported **100% (10/10)** — 80 points of inflation. Negative
  control after the fix: one called and one uncalled function reports
  **50% (3/6)**, not 100%. No-regression control: a genuinely fully-executed
  file still reports 100% (9/9).

  Residual, left open and bounded: flattened module top-level statements still
  file under `<entry>`, so one fixture reports 66% (2/3) where honest is 3/3.
  That direction **under**-reports and is bounded at ≤2 lines (≤0.9%) per
  campaign module. A `ModuleExecScope` guard was built and then **reverted** —
  it did not reach the flatten path, and `CURRENT_EXEC_MODULE` also feeds
  overload tie-breaking, so it carried regression risk for no proven benefit.
  Also filed: `record_condition_coverage` has the same hardcoded `"<source>"`
  at ~12 sites. Side effect of the fix: the debugger's breakpoint file
  matching consumed the same placeholder and is now repaired.
  Detail: `doc/08_tracking/bug/coverage_cross_file_line_conflation_2026-08-04.md`.

**The gate is still doing work — do not relax it.** Defect B was closed by
making instance-method calls genuinely reach `record_function_call`, never by
loosening the reporter, which would have inflated every number in the repo
while measuring nothing. Three independent checks pin this: a purpose-built
negative-control probe with one called and one uncalled method reports
**41% (5/12), not 100%**, and both uncalled symbols stay absent from the dump;
free-function counts are unchanged to the digit across arms
(`_dom_attr` 333215/333215), proving no double-counting; and binary identity
was established by positive capability probe — the pre-fix binary emits
ABSENT for every method name, the fixed one emits real counts.

Tests were written only for lines that were genuinely untested AND measurable;
while defect B was open, lines it made unmeasurable were listed rather than
tested, since a test against them would have raised apparent effort while
moving nothing. Unreachable-by-construction lines are argued individually in
the landing commits, never folded silently into a percentage.

Defects found and filed by this campaign (all in `doc/08_tracking/bug/`):
seed runner 600s child kill (fixed `fd381db82bc`), render-session second-render
arm shadowing (fixed in `6eb19236c05`), heuristic size whitelist painting
24x16 (fixed in `6eb19236c05`), JIT nil-`.lower()` in backend auto-resolve
(open), seed `.?` bool-lowering crashing the CUDA resolve arm (worked around,
family open), coverage tooling inert (fixed) / under-attribution (open).

### Per-phase offload status (2026-08-04)

Presenter-lane audit of the browser_engine render pipeline
(tokenize → dom → style → layout → paint → tiles → present). "GPU-shaped"
means the phase computes a GPU-friendly flat/table projection verified against
the CPU oracle but has no device dispatch in the production path (zero
engine2d/`rt_gpu`/device references in the phase modules).

| Phase | Modules | Status | Probe-gated fallback |
|---|---|---|---|
| tokenize | `html_tokenizer.spl` | CPU-only; GPU-shaped flat projection (24/24 parity) | n/a — no device lane |
| dom build | `html_tree_builder.spl`, `dom.spl` | CPU-only; offload-shaped build parity (38/38) | n/a — no device lane |
| style | `style_block_parse.spl`, `style_block_resolve.spl`, `selector_matcher.spl` | CPU-only; GPU table projections (47/47) + decl apply (61/61) | n/a — no device lane |
| layout | `simple_web_html_layout_renderer*.spl` | CPU-only; emits `WebGpuPaintFrame` for the paint lane | n/a — no device lane |
| paint | `simple_web_html_engine2d_presenter.spl` (economics + gpu-first) | GPU rect-fill lane; glyph/gradient/image residual stays CPU ground truth (bit-exact by construction) | yes — backend verdict + engine2d create probe; per-frame decision string marks every decline |
| tiles | `simple_web_html_layout_renderer_paint_tiles_gpu.spl` | GPU tile lane via Engine2D Vulkan | yes — `Engine2DReadback` source + `vulkan_cpu_fallback_reason` provenance |
| present | `simple_web_html_engine2d_presenter.spl` (`_present_gpu_first`) | gpu-first default (`SIMPLE_WEB_GPU_PAINT` unset); `device_readback` + device identity for any offload claim | yes — fail-closed resolved-backend probe (vulkan/software); create-failure fallback marked `cpu-fallback` |

Remaining CPU-only phases (tokenize, dom, style, layout) have no production
device dispatch today; their GPU-shaped projections are the prepared
offload surface.

**Gate status: the present row is GREEN — `Results: 17 total, 17 passed, 0
failed` (with presenter spec 5/5 and showcase 13/13), restored in
`20a82c77cfa`.**

An earlier revision of this section claimed the row was RED at
`Results: 17 total, 12 passed, 5 failed` and attributed it to the gpu-first
default. **That attribution was wrong and is retracted.** In a pristine
worktree the parity gate measured 17/17 at `3ddd017c87d` with the base
presenter and no fix; the red reproduced only in the shared working copy,
which was carrying ~6,300 lines of another session's uncommitted
Engine2D/Vulkan work executed from source, amplified by host load driving
`budget-break`. The decisive tell: the fifth failing example ("direct
Engine2D lane render", `expected nil to be greater than 0`) exercises
`_render_lane_direct`, which calls `Engine2D.create_requested_backend` /
`present()` / `read_pixels_with_source()` directly and never touches the
presenter — so no presenter change could have caused or cured it. That
session's work landed separately as `28288f98102`.

The mirroring defect was nonetheless real and is fixed: the
`fill_op_count == 0 or fill_pixels == 0` decline branch in `_present_gpu_first`
no longer mirrors an unusable GPU frame via `_cpu_mirror_for_frame`; it
re-runs `simple_web_layout_render_html_readback_paint`, matching the
explicit-CPU declines above it. The decline branch executed in every green run
(decision marker present), so the green is not vacuous. Detail:
`doc/08_tracking/bug/web_gpu_first_default_publishes_empty_frame_2026-08-04.md`.

**Closed (`1e461e1985c`):** the `gpu-full`/`gpu-partial` prefix derived from
`economics.residual_pixels` — a pre-dispatch prediction — rather than
`readback.source`, so it could over-claim while `source=` stayed honest. The
prefix *and* the `offloaded=` claim are now both gated on the existing
`_web_gpu_readback_device_proven` predicate (`source == device_readback` ∧
`handle > 0` ∧ `identity > 0` ∧ `pixel_count == frame_pixels`); relabelling
the prefix alone would have left an unearned `offloaded=`. Measured on a real
`webgpu` frame:

```text
before: gpu-first:gpu-full:offloaded=rect_fill:2ops/1760px:cpu=none:source=cpu_mirror:handle=0:device_identity=0
after:  gpu-first:cpu-presented:offloaded=none:cpu=full-frame:reason=readback-not-device-proven:source=cpu_mirror:handle=0:device_identity=0
```

`vulkan` and `cuda`, which are genuinely device-proven on this host, are
byte-identical before and after.

Two prior claims about this item were wrong and are corrected. The leak was
**not** "any CPU source": the decline branch already returned early on
`source == "cpu_fallback"`; what escaped were the *other* CPU sources, since
`present_gpu_paint_readback` returns whatever `read_pixels_with_source()`
reports on its `Ok(engine)` branch, so a backend that constructs successfully
but presents in software yields `cpu_mirror` and fell through to `gpu-full`.
And the edit was **not** blocked by gate vocabulary: exactly one spec
(`web_gpu_first_present_decision_spec.spl`) asserts on these strings — neither
the parity nor the showcase gate mentions them — so **no existing assertion
had to change**. One example was *added*, sweeping all six candidate backends
and asserting both directions, because the pre-existing spec only probes
`vulkan` on this host and therefore never reached the over-claiming branch;
without it the fix would have shipped unpinned.

**Closed (`ddaa072028e`), and the mechanism was worse than this document
previously stated.** The earlier entry said `_backend_is_cpu()` "does not
recognise `cpu_mirror` / `cpu_fallback`". It is in fact a **type confusion**:
`_backend_is_cpu` classifies backend *names* (`software`, `cpu`, `cpu_simd`,
`simd_cpu`, `cpu-simd`), and it was being handed `out.source`, a readback
*source*, drawn from a fully disjoint vocabulary (`device_readback`,
`cpu_mirror`, `cpu_fallback`, `not_requested`, `completion_unknown`,
`readback_failed`, `device_identity_unknown`, `swapchain_present`,
`framebuffer_surface`). No source string can ever be in that set, so the
predicate returned `false` for **every possible input** and
`gpu_backend_used` was a constant `true` — it could not have been false for
any backend. `webgpu` was not a special case, only the case that happened to
be noticed; `cpu_simd`, a literally-named CPU backend, also reported
`gpu_backend_used=true`.

The flag now uses `_web_gpu_readback_device_proven`, the same predicate as the
decision string, and the marker also emits `handle=` / `device_identity=`:

```text
before  webgpu    source=cpu_mirror       gpu_backend_used=true
after   webgpu    source=cpu_mirror       gpu_backend_used=false
before  cpu_simd  source=cpu_mirror       gpu_backend_used=true
after   cpu_simd  source=cpu_mirror       gpu_backend_used=false
        vulkan    source=device_readback  gpu_backend_used=true   (unchanged)
        cuda      source=device_readback  gpu_backend_used=true   (unchanged)
```

A print-only diagnostic cannot be asserted against, so the record is now
exposed via `web_gpu_paint_last_dispatch_receipt()`, reusing the receipt
pattern already in this tree; the guarding example sweeps seven backends in
both directions.

The rest of the provenance family was audited and found honest: the
`[web-gpu-paint-measure]` marker and the cpu-raster / cpu-fallback /
`cpu-presented` declines are already gated, the DrawIR receipt reports the
requested `backend=` *and* the actual `source=` without a boolean claim, and
the engine2d `*Evidence` classes echo the requested backend name while making
no usage claim. Two sites are deliberately left alone:
`hardware_acceleration_verified` is parsed out of Chrome's own JSON rather
than asserted by us, and `cpu_job_verdict="cpu-paint-offloaded"`
(presenter:276) is a pre-dispatch economics *prediction*, never a report of
what ran — renaming it would edit strings three specs assert on.

**Open — gate flakiness, filed separately:** the parity spec probes for a
backend at `web_engine2d_gpu_offload_parity_spec.spl:258` and calls
`Engine2D.create_requested_backend` later, so under host contention the probe
can answer `vulkan` while the create returns `cpu_fallback` — observed live as
`16 total, 16 passed, 1 failed` with
`[offload-provenance] lane=vulkan source=cpu_fallback handle=0 identity=nil`
under 34 concurrent `simple` processes. The re-run measured 17/17 **only
because the lane resolved to `software` and the GPU branch was skipped**, so
both arms are untrustworthy: the red is a false failure and that green is
vacuous while being indistinguishable from a real one. The gate cannot
currently tell "GPU worked", "GPU unavailable" and "GPU vanished mid-test"
apart. Any fix must keep the spec able to fail — a repair that removes the
red is worse than the flake.

**Process note for anyone reading a gate verdict from this tree:** a red
measured in the shared working copy is not evidence about origin. This
checkout routinely carries thousands of lines of other sessions' uncommitted
`src/**`, and `.spl` libraries execute from source. Reproduce in a pristine
worktree at a named sha before attributing a regression to a commit.

## Acceptance

The parent plan's gates apply verbatim (§14): byte-matching mutation
journals, canonical serialization parity, semantic checksums, fail-closed
capacity overflow, no hidden SoftwareBackend calls, and promotion only on
measured p50/p95 event-to-present improvement including transfer +
synchronization cost.
