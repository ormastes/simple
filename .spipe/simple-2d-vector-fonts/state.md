# Feature: Simple 2D Vector Fonts

## Raw Request
`$sp_dev check vector font support on simple 2d. which is seems not exists now. revive, it. and improve fonts supports and font rendering perf bugs. do with smaller agents with guides and design and higher mdodel review after finished.`

## Task Type
feature

## Refined Goal
Restore production-usable vector-font loading and text rendering in Simple 2D, broaden supported font behavior, and remove measured font-rendering performance defects without regressing existing bitmap-font or backend behavior.

## Acceptance Criteria
- AC-1: A repository audit identifies the current vector- and bitmap-font paths, their callers, any previously removed or disabled vector-font implementation, and the exact supported/unsupported formats and text behaviors.
- AC-2: Simple 2D can load at least one repository-owned vector-font fixture through its public drawing facade and render deterministic nonblank glyph pixels at two sizes, with invalid or unsupported font input failing safely.
- AC-3: Text layout/rendering proves multiple glyphs, whitespace, baseline/advance handling, repeated glyphs, and at least one non-ASCII glyph supported by the chosen fixture; bitmap-font behavior remains covered.
- AC-4: The implementation reuses the existing font/rasterization dependency or owner module where one exists, adds no speculative font abstraction, and introduces no raw runtime shortcut outside an approved owner boundary.
- AC-5: A retained baseline and after measurement on the same representative text fixture show the changed hot path improves repeated text rendering or eliminates a diagnosed scaling/allocation defect; the report records timing, cache state, backend, dimensions, RSS/memory when available, and output checksum/readback proof.
- AC-6: SSpec scenarios use real absolute pixel/layout/cache assertions, include manual-facing `step()` flow, reject empty/same-path equality as proof, and generate an operator-readable Markdown manual with zero stubs.
- AC-7: Focused correctness checks, the relevant Simple 2D/GUI sanity check, the optimizer check for touched `.spl` files, dependency checks for changed entrypoints, direct-runtime guards, and the generated-spec layout guard pass once after convergence.
- AC-8: Architecture, detail design, test plan, agent task plan, relevant Simple 2D/font guide, generated spec manual, and stack architecture/TLDR are current and trace the selected REQ/NFR requirements to implementation and tests.
- AC-9: A normal/highest-capability reviewer inspects the merged research, requirements, design, generated manual, implementation, performance evidence, and exclusions before final verification accepts the lane.

## Scope Exclusions
- Complex-script shaping, hinting parity with every platform font stack, new font-file formats, and cross-platform GPU font offload are excluded unless research shows they already exist and only require reconnection.
- No release/version bump is included unless separately requested after verification PASS.

## Cooperative Review
- Lower-model sidecars: local source/history audit; external font-rendering prior-art/performance research; existing test/evidence and documentation audit.
- Merge owner: primary Codex agent (`/root`).
- Final reviewer: primary normal/highest-capability Codex agent after sidecars and implementation complete.
- Provisional shared public interface names: preserve the existing Simple 2D facade; use discovered owner names rather than creating parallel `VectorFont`/`FontRenderer` APIs.
- Manual `step()` flow names: `Load a vector font fixture`, `Render text through the Simple 2D facade`, `Verify glyph layout and pixels`, `Render the same text again`, `Verify cache and performance evidence`, `Reject invalid font input`.
- Setup/checker helper names: `load_vector_font_fixture`, `render_font_fixture`, `expect_nonblank_font_pixels`, `expect_antialiased_font_pixels`, `font_render_perf_probe`; sidecars must report existing equivalents before any helper is added.
- Fail-fast placeholders: any temporary scenario/helper body uses `fail("vector font implementation pending")`; no placeholder pass or empty body.
- Generated-manual review owner: primary Codex agent.

## Runtime Boundary Decision
- `runtime_need`: bulk glyph-alpha transfer, glyph-presence query, native face generation, and exact UTF-8 path-byte marshaling at the existing `spl_fonts` owner; no feature-local runtime alias.
- `facade_checked`: existing Engine2D, `FontRenderer`, typed `spl_fonts` wrapper, dynamic-library facade, and bitmap/vector fallbacks.
- `chosen_path`: `add-smallest-owner-facade` in the existing `spl_fonts` owner and reuse it through `FontRenderer`.
- `rejected_shortcuts`: raw `rt_*` aliases in feature/tests, fixture-only pixel painters, backend field pokes, hard-coded glyph pixel tables, and same-path fallback comparisons.

## Research Summary
- Engine2D text is bitmap-only; `FontRenderer` already owns TTF -> vector -> bitmap selection.
- The existing stb/font I/O owner is reusable; no owned font fixture or public-facade real-font proof exists.
- Current focused baseline: Engine2D bitmap PASS; font renderer FAIL on unresolved interpreter extern `rt_string_data`.
- Hot risks: linear/copying cache, per-pixel WFFI calls, outline-edge scanning, and per-miss environment parsing.
- Open questions: NONE.

<!-- sdn-diagram:id=simple-2d-vector-font-context -->
```sdn
simple_2d_vector_font_context:
  Engine2D.draw_text: bitmap_default
  FontRenderer: [stb_ttf, builtin_vector, bitmap_fallback, glyph_cache]
  selected: Engine2D -> FontRenderer
  evidence: [owned_fixture, framebuffer_oracle, cold_warm_perf]
```

## Selected Requirements
- Feature B: existing TTF/OTF `FontRenderer` through Simple 2D (`REQ-001..010`).
- NFR B: bounded cache, >=90% warm hits, >=25% warm p50 improvement (`NFR-001..009`).
- Final docs: `doc/02_requirements/{feature,nfr}/simple_2d_vector_fonts.md`; unchosen option docs are absent.

## Design Interface Contract
- Public facade: `Engine2D.load_font(path) -> bool`, `Engine2D.unload_font()`, existing `Engine2D.draw_text(...)`, and `Engine2D.font_cache_stats() -> FontCacheStats`.
- Owner methods: `FontRenderer.try_load_runtime_ttf(path) -> bool`, `FontRenderer.clear_ttf()`, `FontRenderer.cache_stats() -> FontCacheStats`.
- Default: no active TTF means the existing bitmap backend path is unchanged; successful load switches only text calls to cached glyph coverage composited through existing backend image-blend support.
- Manual steps: `Load a vector font fixture`, `Render text through the Simple 2D facade`, `Verify glyph layout and pixels`, `Render the same text again`, `Verify cache and performance evidence`, `Reject invalid font input`.
- Test helpers: `load_vector_font_fixture`, `render_font_fixture`, `expect_nonblank_font_pixels`, and `expect_antialiased_font_pixels`; any temporary body must call `fail("vector font implementation pending")`.

## Design Decision
- Highest-capability merge accepted one tight straight-alpha payload plus one existing image blend; per-glyph readback is rejected, while the current emulation blend may perform one full-frame readback.
- Use live `spl_fonts`; keep the 512-entry FIFO, add 32 MiB payload bound and exact counters.
- One active TTF/OTF face per process is explicit until native per-face handles exist; native generation invalidates renderer caches.
- Architecture, TLDR, detail design, test plan, and reviewed sidecar plan are written on the same feature slug.

## Phase
performance-and-manual-in-progress

## Log
- dev: Created state file with 9 acceptance criteria (type: feature); recorded cooperative lower-model lanes and highest-capability final review.
- research: Three read-only sidecars audited source/history, tests/docs, and domain references; results merged after concurrent cleanup removed the first untracked copies.
- requirements: User selected Feature B / NFR B; final requirements written and option artifacts removed.
- design: Architecture, SSpec/manual, and performance sidecars completed; primary highest-capability merge accepted the design.
- implementation: Added live owner generation/presence/bulk-alpha ABI, fixed `spl_str_ptr`, bounded observable cache, tight-alpha payload, Engine2D routing, deterministic fixtures, and primary SSpec. Cycle 3 found compact assignment syntax and was fixed; verification stopped at the mandatory three-cycle cap.
- resolved-blocker: The earlier self-hosted missing-`ttf_rasterizer` class-shape failure is recorded at `doc/08_tracking/bug/self_hosted_font_renderer_optional_field_shape_2026-07-11.md`; extracting `font_types.spl` and removing eager module construction resolved compilation.
- implementation-follow-up: Extracted shared font types to break the renderer/rasterizer import cycle, moved the renderer into per-engine lazy state, fixed value-semantics write-back and raw-optional cache lookup, corrected the Latin-1 cmap fixture, restored the bitmap nil fast path, and made shutdown unload font resources. Diagnostic native runs now pass all vector-font scenarios and the existing bitmap integration; canonical self-hosted verification remains pending because concurrent work replaced `bin/simple` with a Rust seed.
- performance: Added the 31-pair cold/warm perf spec and cache-bound unit case. NFR-003 remains unproven until a true pre-feature bitmap baseline and pinned host are identified; a same-run bitmap row is retained but is not mislabeled as historical baseline.
- performance-follow-up: The first full-draw row exposed full-frame blend dominance. Promoted `draw_image_blend` into `RenderBackend` and added direct SoftwareBackend framebuffer blending. Highest-capability review rejected the one-entry payload memo because it escaped cache accounting and fabricated glyph hits; it was deleted. The perf spec now measures the public Engine2D path, requires exact glyph-hit deltas and framebuffer checksums, and fails when the retained bitmap baseline is absent.
- final-review-fixes: Lower-model architecture/perf/SSpec reviews identified a borrowed native glyph pointer, synthetic payload-cache hits, weak pixel/layout oracles, optional NFR-003, and a missing direct interpreter regression. Rasterization now returns owned snapshots that the wrapper copies/frees; Rust owner tests pass 7/7. The SSpec has fixed checksum/bbox/anchor/clipping oracles and full invalid-input stat atomicity, and a direct public-facade interpreter probe passes diagnostically.
- baseline-attempt: Created detached pre-feature worktree `/tmp/simple-font-baseline` at `126bfa06081d` with the unchanged bitmap probe. Pure stage3 native-build segfaulted and direct run produced no output; Rust-seed AOT output was invalid, then LLVM failed on `%l10`. No baseline number was accepted. Await restored pure-Simple tooling before one final retained run.
- manual-blocker: Pure stage3 docgen timed out after an older pure candidate segfaulted. No generated manual was hand-authored or substituted with Rust-seed output.
- continuation-review: Small-agent implementation/evidence audits found early-size validation, host-dependent kerning evidence, UTF-8 path/text marshaling, singleton concurrency, and transparent-destination blend concerns. Size validation now precedes native layout; the Rust owner uses serialized repo-owned fixtures with strict nonzero kerning and passes 7/7; the public primary scenario loads a non-ASCII path and layout uses exact UTF-8 bytes. Singleton face/layout scope remains explicit and transparent-destination blending is tracked separately.
- manual-blocker-confirmed: The final untried pure-Simple candidate passed `-c` but segfaulted once in system-spec docgen. Per the retry cap, docgen was not retried.
- blocker-tracking: Recorded the pure-Simple docgen/baseline crash at `doc/08_tracking/bug/pure_simple_spipe_docgen_vector_font_spec_crash_2026-07-11.md`.
