# Feature: Shared Multilingual GPU Fonts

## Raw Request

Update docs, guides, and SPipe skill/process artifacts; port freely licensed fonts covering the top 10 languages and 10 common font categories; build one shared honest GPU font-rendering/offload library with Simple code that emits backend GPU code; integrate that shared font path into both the existing 2D and 3D libraries. Follow `$sp_dev` from acceptance criteria through research/options. Preserve existing dirty work. User selection is mandatory before final requirements or implementation.

## Task Type

feature

## Refined Goal

Provide one configurable, license-audited multilingual font pipeline shared by Simple GUI, Web, 2D, and 3D that shapes on CPU, emits truthful backend GPU programs from Simple, renders through real device paths when available, and retains exact software fallback and evidence.

## Acceptance Criteria

- AC-1: A documented selection rule identifies ten target languages and executable coverage checks prove representative required code points, shaping cases, and fallback for every selected language.
- AC-2: A documented taxonomy identifies ten common font categories and the asset manifest resolves at least one freely redistributable face for every selected language/category obligation without claiming unsupported combinations.
- AC-3: Every imported font records upstream URL/version, SPDX-compatible license, copyright/attribution, immutable checksum, supported formats, and redistribution/subsetting rules; missing or incompatible metadata fails closed.
- AC-4: One shared Simple font library owns face discovery, configuration, shaping inputs, glyph cache keys, bitmap/vector glyph material, backend program emission, capability reporting, and CPU fallback; GUI/Web/2D/3D do not fork those contracts.
- AC-5: Simple source emits inspectable backend programs for the selected GPU targets, and emission tests assert backend syntax/entry markers without pretending emission is device execution.
- AC-6: Native device tests separately prove backend selection, submitted glyph payload, fence/device marker, readback provenance, nonblank absolute pixel oracle, and CPU parity; unavailable hardware is reported as unavailable rather than passed by simulation or mirror.
- AC-7: Existing 2D and 3D public font entrypoints delegate to the shared path while their current behavior remains available behind explicitly deprecated compatibility adapters until parity and reference-removal gates pass.
- AC-8: Bitmap and vector fonts use one runtime configuration surface for family, category, language/script fallback, size, weight, style, hinting, antialiasing, atlas policy, and preferred/suggested/required execution target.
- AC-9: Cache keys include font checksum, face/variation identity, glyph/run, rendering configuration, scale/transform, backend/device features, emitted-program version, and dependency generation; bounded caches expose hit/miss/eviction/bytes counters.
- AC-10: Equal-semantics benchmarks record shaping, emission/JIT/cache, upload, queue, GPU, readback/present, CPU, RSS/VRAM, fallback, viewport, host, and checksums; NFR thresholds are selected by the user before implementation.
- AC-11: SSpec scenarios use `std.spec.*`, imperative `step("...")` flows, structured DrawIR/object evidence before pixels, absolute glyph oracles, corrupt/missing payload rejection, real assertions, and generated manuals with zero stubs.
- AC-12: Final verification checks all changed `doc/06_spec`, `doc/07_guide`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, and `.gemini/commands` process artifacts; stale font-offload or evidence instructions fail the lane.
- AC-13: No new raw runtime shortcut, backend field poke, fixture-only device bypass, duplicated rasterizer, or third-party dependency is added where an existing facade/library/native font facility suffices; decisions are recorded before runtime-adjacent changes.
- AC-14: Existing dirty work is preserved, and changes for this lane remain identifiable separately from prior vector-font and GUI/GPU architecture work.

## Scope Exclusions

- Implementing or importing font binaries before feature and NFR selection.
- Replacing text shaping with a GPU kernel; shaping and semantic fallback remain CPU-owned unless later evidence supports a separately selected extension.
- Claiming native GPU execution from emitted source, probe success, upload-only evidence, CPU mirrors, or simulation.
- Designing a second 2D/3D font API when an existing contract can be extended.

## Cooperative Review

- Intensive Spark/small-model lanes: local shared-path/code reuse; font
  licensing/language/category coverage; backend emission/device evidence;
  2D integration; 3D integration; executable-spec/manual matrix; and
  doc/guide/SPipe freshness.
- Merge owner and final normal/highest-capability reviewer: primary Codex agent.
- Reviewed shared vocabulary: canonical `FontRenderer`; one possible
  `FontRenderBatch`/`prepare_text` material seam only if persistent shared atlas
  evidence requires it. No parallel renderer/emitter hierarchy.
- Manual flows: `step("Load a licensed multilingual font manifest")`, `step("Shape and rasterize the same glyph run through 2D and 3D")`, `step("Emit the selected GPU backend program")`, `step("Prove native submission and compare device readback with the CPU oracle")`.
- Setup/checkers: `setup_shared_font_fixture`, `expect_font_license`, `expect_language_coverage`, `expect_backend_emission`, `expect_font_render_parity`.
- Any temporary helper must call `assert(false)` or `fail(...)` with the missing capability; no silent placeholder is acceptable.
- Generated-manual review owner: primary Codex agent after sidecar merge.

## Runtime Boundary Decision

- runtime_need: none during dev/research/options.
- facade_checked: deferred to local research before any implementation proposal.
- chosen_path: `reuse-facade` by default.
- rejected_shortcuts: raw font/GPU `rt_*` aliases, environment-only fake payloads, direct backend field pokes, hard-coded captured glyph pixels, and fixture-only device branches.

## Research Summary

- Reuse `FontRenderer`, the incomplete Pure Simple shaping/BiDi owners, the
  existing portable GPU emitter, Engine2D evidence ladder, and engine texture
  APIs; complete shaping and add the missing font Vulkan artifact without a
  second parser, rasterizer, emitter, or cache abstraction.
- The existing registry silently uses Korean while the provisional
  total-speaker list uses Indonesian. No list becomes authoritative until its
  source table/release, counts, ties, and language policy are pinned.
- The proposed ten font kinds are product coverage categories, not a popularity
  ranking. Coverage is a sparse licensed matrix, not a fabricated 10x10 claim.
- CPU shapes and, for the recommended first lane, rasterizes. GPU programs
  sample/compose shared atlas material. Current Metal precedent is real;
  emission, CPU mirrors, and environment payloads do not prove device execution.
- 3D completion requires real texture upload/binding, HUD/world transform,
  clipping/depth, draw/dispatch, fence, and device-origin readback evidence.
- High-capability review rejected the first bundled A/B/C/D choices and split
  language, category, shaping, glyph-material, and packaging decisions.
- Research: `doc/01_research/{local,domain}/shared_multilingual_gpu_fonts.md`.
- Selected requirements: `doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`.

## Review Evidence

- Small-model spec audit: four core specs (`manifest`, `surfaces`, `emission`,
  `native readback`) plus generated-manual audit; exact rows wait for selection.
- Small-model docs audit: final requirements, architecture/design/test plans,
  UI/2D/3D/font guides, font notices, executable manuals, and the font-specific
  `.claude/skills/spipe.md` evidence recipe require post-selection refresh.
  Generic agent/skill instructions change only if workflow semantics change.
- Small-model option review found and the primary reviewer corrected ranking
  provenance, taxonomy labeling, shaping incompleteness, 3D binding evidence,
  GPU-honesty language, NFR protocol, and biased option bundling.
- Second intensive sidecar pass found packaging/NFR incompatibility, missing
  format and native-promotion choices, stale interface names, and current
  Engine3D/Vulkan/color-font limitations. Primary review added F/G/P3 choices,
  reproducible derived language manifests, and the minimal canonical seam.
- Asset candidates remain research leads only: none has yet passed the required
  immutable version/checksum/copyright/RFN/script-coverage manifest gate.
- Ranking pass and primary review reject L1 as the default: no pinned public
  redistributable L1+L2 table is available. L2 now pins CLDR 48.2 tag/commit,
  source hashes, deterministic aggregation, alias/macrolanguage/tie policy, and
  tenth/eleventh boundary evidence.
- Font-manifest pass found a pinned 16-file Google Fonts candidate catalog but
  no accepted binaries. Primary review resolved the F1/P1 variable-font clash
  by allowing only unchanged `glyf` default instances; non-default axes fail
  closed. Checksums, embedded metadata, tables, sizes, and coverage await the
  mandatory selection.
- Primary regeneration of pinned CLDR 48.2 corrected the final rows to
  `en,zh,es,hi,ar,fr,pt,ru,ur,id`; Bengali is rank-11 cutoff evidence. The
  annotated tag object peels to source commit
  `11299982335beb974c1c63c45265184e759c0f41`.

## Selected Requirements

- User accepted the planned recommendation on 2026-07-11:
  `L2+C1+S1+F1+R1+P1+G1`, NFR A.
- Final requirements:
  `doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`.

## Frozen Cooperative Interfaces

- Existing owner: `FontRenderer`.
- Minimum new material values: `FontRenderQuad` and `FontRenderBatch` in
  `text_layout/font_types.spl`; `FontRenderer.prepare_text(content, color,
  font_size) -> FontRenderBatch` reuses `render_text_payload` and cache
  generation rather than adding another renderer/cache.
- Existing emitter extension:
  `emit_portable_font_atlas_composite_kernel(target) -> PortableComputeArtifact`;
  no `GpuFontEmitter` class.
- Existing Engine2D entrypoints stay unchanged and consume the batch internally.
  Minimal Engine3D additions are
  `draw_text_hud(x: i32, y: i32, text_val: text, color: u32, font_size: i32)
  -> bool` and `draw_text_world(x: f32, y: f32, z: f32, text_val: text,
  color: u32, font_size: i32) -> bool`, plus matching `load_font`/`unload_font`;
  both consume the same batch. World coordinates project through the stored
  view/projection matrices; CPU is fallback evidence, never native promotion.
- Manual steps: `step("Load the pinned multilingual font manifest")`,
  `step("Prepare one shared font batch for 2D and 3D")`,
  `step("Emit the selected font composite program and plan compilation")`, and
  `step("Prove native submission and device readback")`.
- Setup/checkers: `setup_shared_font_fixture`, `expect_font_license`,
  `expect_language_coverage`, `expect_shared_font_batch`,
  `expect_backend_emission`, and `expect_font_render_parity`.
- Any unavailable helper fails with `assert(false)`/`fail(...)`; no silent
  placeholder or environment-only success is accepted.

## Phase

implementation-in-progress; native Engine3D promotion and executable verification remain

## Log

- dev: Created state file with 14 acceptance criteria (type: feature); implementation is selection-blocked.
- research: Three initial bounded sidecars plus three intensive Spark-style
  audits completed; primary/highest-capability review corrected the artifacts.
- selection: Accepted `L2+C1+S1+F1+R1+P1+G1`, NFR A; option artifacts removed
  and final requirements written.
- design: Architecture, detail design, four-spec test plan, and bounded sidecar
  task plan written and primary-reviewed.
- assets: Bundled 16 unchanged Google Fonts binaries plus adjacent metadata and
  licenses under `assets/fonts/google-fonts`; SHA-256 and aggregate 51,764,704
  bytes independently verified. Registry exposes the CLDR top ten, rank-11
  cutoff, immutable asset records, and complete 100-cell sparse matrix.
- material: `FontRenderer` owns a bounded persistent shelf atlas with stable
  per-glyph quads, dirty regions, generation/invalidation, and zero-config
  bitmap/vector fallback layout. Engine2D consumes batch glyph subrects through
  its blend surface; Engine3D exposes CPU HUD/world compatibility consumption.
- emission: Existing portable emitter now produces versioned per-quad atlas
  composition for CUDA/HIP/OpenCL/Metal/WGSL; Vulkan remains separate.
- process/docs: Canonical guide/index, UI/pixel/Engine3D guides, legacy Unicode
  design, notices, changelog, and `.claude/skills/spipe.md` updated.
- verification: Manifest, emission, and shared-surface SSpecs plus manual drafts
  exist. Native readback spec/generated manuals/perf gates remain. The shared
  self-hosted compiler was unavailable. The Rust seed is not accepted as the
  production toolchain. Three isolated pure-Simple bootstrap lanes
  were attempted and stopped at the mandated cap: Cranelift verifier error;
  LLVM `bitcast void`; llvm-lib unresolved intrinsics/undefined locals with an
  explicitly broken object. Logs are under `build/mini_builds/`; no shared
  compiler was replaced and no failing command will be rerun this session.
- intensive review: Small-model static passes were accepted only after primary
  review corrected zero-config `prepare_text` fallback layout, malformed glyph
  atlas bounds, tier-facade exports, Engine3D transparent-padding composition
  and live target dimensions, portable OpenCL casts, and CPU/GPU alpha parity.
  The manifest SSpec now hashes every real binary through the owned package
  facade and reads nonempty notices, including Roboto Slab COPYRIGHT evidence.
  Overstated REQ/NFR trace tags were removed. Exact multiscript shaping/corpus
  acceptance, native Engine3D device proof, generated manuals, and performance
  evidence remain intentionally incomplete.
- shaping/corpus review: Existing Skia shaping was rejected as a shortcut: it
  cannot feed glyph IDs/faces into the codepoint-keyed renderer and lacks the
  required complete Unicode/GSUB/GPOS/cluster/language surface. The prerequisite
  is tracked in `doc/08_tracking/bug/shared_font_pure_simple_shaping_gap_2026-07-11.md`.
  A focused real-font raster/layout witness gate was added, but all candidates
  remain explicitly provisional; the coverage matrix now honestly reports 74
  `unavailable` and 26 `not-designed-for-script`, with no native/fallback
  promotion before exact shaping-corpus evidence.
- native review: Engine3D, Vulkan3D, and WebGPU3D remain CPU/`emu_*`. The
  alternate legacy Vulkan facade has incompatible zero-stubbed ABI, while the
  canonical Vulkan runtime does not expose image upload/download, descriptor
  binding is a no-op, pipeline layouts are empty/hard-coded, and fences are not
  connected to graphics submission. No native patch or readback spec was
  accepted; the existing Engine3D dispatch tracker remains the owner.
- shared 2D/3D material: The pure atlas bounds, alpha-color application, and
  subrect extraction routine now lives beside the generated GPU sources in
  `common.gpu.font_atlas_composite`; Engine2D CUDA/Metal/fallback and Engine3D
  CPU compatibility all call it. No fake 3D GPU lane was added: Engine3D still
  requires a real device-backed scene target before native font promotion.
- emitter/docs review: Native-target font kernels now take true atlas/destination
  element counts and guard computed indices; WGSL also guards its parameter,
  atlas, and destination storage lengths. Metal emission now follows the owned
  MSL header + `constant FontAtlasCompositeParams& [[buffer(2)]]` pattern rather
  than invalid unbound scalar parameters. Source-contract checks and the manual
  were updated. OpenCL host dispatch was added later; no target compiler ran.
  Architecture/design/manual/SPipe text was corrected to
  distinguish current CPU compatibility/provisional coverage from target native
  behavior and to remove false REQ-012/NFR claims.
- static manifest schema: Candidate records now include extracted embedded
  style/full/PostScript names, version, default variable axes, closed fallback
  role, and one hashed `assets/fonts/google-fonts/CORPUS.sdn` witness reference.
  Focused manifest checks cover nonempty/closed fields, representative exact
  values, and the real corpus hash. This improves REQ-004 metadata integrity but
  does not promote any face without the blocked shaping/corpus acceptance run.
- resumed intensive audit (pre-input milestone): A fresh Spark static-compile pass found no P0/P1 in
  the scoped font-lane Simple edits; representative embedded names were also
  checked directly against the bundled binaries. No compiler was run. At that
  milestone CLDR regeneration was impossible offline because the three pinned
  XML inputs and peeled CLDR object were absent, while the only general
  `parse_xml` was an identity stub. The accepted minimal path was one
  targeted attribute scanner plus fixed-decimal aggregation/double render.
  Generated host dispatch remains unwired for CUDA/HIP, Metal, and WGSL because
  they require different argument packing/binding. Metadata-only selection was
  rejected; OpenCL is the first real adapter with upload, launch, and sync, but
  required device-readback evidence has not run.
- CLDR ranking core (pre-input milestone): Spark implemented `common.encoding.font_cldr_rank` and a
  focused fixture for exact fixed-decimal contribution, half-up rounding,
  aliases, territory-aware likely scripts, per-script totals, and deterministic
  ties. High-model review added comment skipping, duplicate/nesting failures,
  macrolanguage-alias exclusion, and deterministic `und` exclusion. This is core-only: no
  compiler ran; at that point the pinned CLDR 48.2 XML/hash inputs were absent,
  the scanner was not a validating XML parser, and REQ-001/REQ-002 remained
  unverified.
  Final high-model delta review passed after canonical base-alias merging gave
  explicit source script/region fields precedence over replacement fields.
- CLDR pinned-input slice: the exact three `release-48-2` supplemental XML
  files and Unicode-3.0 license are now bundled with a 179-byte annotated-tag
  witness whose Git tag object is `fc1fd058...`, a source manifest, and a
  deterministic top-eleven ledger. Fresh upstream Git and SHA-256 checks match
  the pinned tag, peeled commit, and all stored digests. Independent exact
  recomputation corrected six stale registry totals by one to three people and
  added script subtotals. The system scenario now hashes real bytes, regenerates
  twice, compares the full ledger, and checks every registry row. No Simple
  compiler/test ran under the exhausted cap, so REQ-001/REQ-002 await execution;
  the targeted scanner also remains non-validating XML.
  Final high-capability review independently replayed all 1,589 contributions,
  tag/commit and file hashes, top-eleven totals, script subtotals, and exact
  serialized newline format; source/manual review passed.
- shaping progress: the existing shared script detector now classifies
  Cyrillic and Urdu Arabic-extension ranges, with a focused fixture.
  `FontGlyphRun` also carries the exact live face handle/generation and logical
  codepoint clusters; the renderer validates that pair and all parallel vector
  lengths before glyph-ID rasterization. This removes generation-only reverse
  binding but does not claim UTF-8 byte clusters, complete GSUB/GPOS, language,
  or accepted complex shaping.
- per-face shaping input: `Shaper` stores replace-by-handle OpenType snapshots
  and resolves them only after fallback chooses a run font. Exact
  handle/generation liveness is required; stale or unbound attached faces do
  not borrow the last/global blob. A primary+emoji fallback fixture preserves
  the selected face through neutral material and rejects it after free. This
  fixes mixed-face input identity, not GSUB/GPOS completeness or corpus
  promotion.
- GSUB Single parser foundation: absolute lookup/subtable offsets are validated
  against the owning GSUB table, Coverage formats 1/2 and SingleSubst formats
  1/2 fail closed, and focused fixtures include cross-table rejection. The
  shaper remains identity because Script/LangSys/Feature activation is not yet
  implemented; no substitution-complete claim is made.
- selector rejection/reuse audit: two Spark reuse lanes found no existing
  portable shaper—fontdue, FreeType, stb, and browser canvas cannot return the
  required shared glyph material; host HarfBuzz is undeclared/non-portable and
  Rustybuzz would violate selected Pure Simple REQ-007. A Spark selector draft
  was deleted after independent Spark and higher review found section aliasing,
  incomplete selected-script routing, unsafe completion semantics, and weak
  tests. The replacement contract requires one integrated, section-bounded
  selector/application slice for `latn/cyrl/hani/deva/arab`, with every active
  unsupported lookup retained as incomplete.
- OpenCL source ownership (pre-host milestone): compiler emission and Engine2D
  runtime compilation were first unified on
  `common.gpu.font_atlas_composite` for the exact versioned kernel source.
  At that milestone host launch and atlas lifecycle still remained promotion
  gates; the subsequent host slice below implements them at source level.
  Spark runtime/docs audits were merged and the final high-capability delta
  review passed after signed-index guards, exact runtime-source ownership
  coverage, and Cyrillic fallback-selection coverage were added. The shared
  OpenCL source also passes Clang OpenCL 1.2 syntax checking with warnings as
  errors.
- OpenCL host slice: Spark audits froze the 15-argument long ABI, runtime-chosen
  local workgroup, concrete Engine2D alias, persistent generation-keyed atlas,
  and prefix fallback. `OpenClSession` now binds and launches the shared entry;
  `OpenClBackend` uploads on generation change, synchronizes, and preserves
  device/mirror state; `Engine2D.draw_text` falls back from the first
  unsubmitted quad. Load/unload invalidates generation collisions. A
  conditional 1x1 device-origin pixel oracle and fail-closed fixtures were
  added. Final high-capability review passed after emitted-kernel overflow
  guards and reload invalidation were fixed. No Simple test/compiler ran, so
  this is implemented source, not native promotion evidence.
- Common/Inherited run resolution: Spark implemented neutral classification and
  one linear forward/backward resolution pass. ASCII non-letters, combining
  ranges, variation selectors, and join controls now inherit the preceding
  strong script, otherwise the following one, with Unknown boundaries failing
  closed; unresolved Inherited runs retain the primary face. Focused fixtures
  cover leading/trailing/between-script and long neutral sequences. Higher
  review passed; no Simple command ran, so this remains static source evidence.
- Shaped material completion gate: `shaped_run_to_font_glyph_run` now requires
  `substitution_complete` in addition to exact-face glyph validity and metadata
  integrity. Direct Latin/emoji cmap witnesses remain non-renderable until the
  selected GSUB plan completes; a focused synthetic completion branch preserves
  the future accepted path.
- Integrated GSUB selector attempt 3 was fully removed after Spark and higher
  review found LangSys activation, Arabic/Indic masking, cross-parent shared
  validation, FeatureParams/FeatureVariations, and structural-validator gaps.
  Per the three-cycle guard, no further selector retry occurs this session.
- Engine3D native-HUD prerequisite: Spark added a neutral Simple-owned MSL
  contract and an Engine3D-tier checked 20-byte vertex packer. Higher review
  rejected and removed the accompanying native runtime draft (unsafe
  interpreter readback, format ambiguity, unchecked GPU completion, unproven
  child cleanup, and no macOS compile evidence). The retained source makes no
  execution claim. Web producers lower through web semantic/layout and GUI
  producers through canonical widget/scene owners; both emit Draw IR. The
  Engine2D executor may lower text to transient vector font batches and must
  not consume this adapter as a parallel path.
- Bundled font-provider port: higher guidance froze the existing provider seam;
  two Spark lanes made all 16 manifest assets addressable by exact trimmed,
  case-insensitive family and added manifest-order/adversarial fixtures. Encoded
  `@font-face` priority and generic CSS heuristics are unchanged. Independent
  Spark and higher reviews passed. This is runtime selection, not coverage-cell
  promotion; shaping acceptance remains required.
- cmap12 slice: Spark confirmed eight bundled candidates carry format 12 and
  Noto Emoji maps `U+1F600` only there. The Pure Simple cmap owner now validates
  Unicode records, sorted/non-overlapping groups, table bounds, scalar range,
  and glyph overflow; Windows 3/10 format 12 precedes conflicting format 4.
  Emoji, truncation, precedence, and non-Unicode rejection fixtures were added,
  and final high review passed. This fixes parser correctness only: one global
  `OtFont`, identity GSUB, and the then-missing glyph-index renderer seam still
  blocked mixed-face acceptance; the next slice closes only the renderer seam.
- shaped glyph-index seam: Spark audits found the existing runtime already owns
  face-specific indexed bitmap/advance entrypoints. Pure Simple now exposes
  those through the canonical rasterizer, keys the existing cache and atlas by
  face + lifetime generation + glyph index + size. The Pure Simple font owner
  rejects freed/stale handle generations, while `shaper_with_ot_face` accepts
  material only when blob cmap IDs equal the live runtime face's IDs for every
  source codepoint. A neutral `FontGlyphRun` preserves the batch-only engine
  boundary; unbound, mismatched, stale, or fabricated IDs fail closed. This
  did not yet wire automatic `draw_text` or per-fallback `OtFont` at that
  milestone, and still does not complete full
  GSUB/GPOS/BiDi, bearings,
  or Engine3D shaped-run submission. No Simple compiler/test was rerun because
  the session's three-attempt cap was already exhausted.
  Final high-capability source review passed after adding revocable handle
  generations, exact blob/runtime cmap parity, explicit Arabic missing-map
  state, and the neutral engine-layer value.
- Engine3D neutral-run slice: the existing CPU HUD compositor is now the single
  `FontRenderBatch` consumer for both text and `FontGlyphRun`; HUD and world
  adapters share strict stale-generation/material rejection. World placement
  reuses the established view/projection anchor and remains a constant-size
  screen-space billboard without depth, occlusion, native texture/draw, or GPU
  proof. Focused live/malformed/stale and visible/behind fixtures were added;
  no Simple compiler/test was rerun under the exhausted three-attempt cap.
  Final high-capability source review passed after replacing the sibling-private
  blend import, routing glyph lookup through the live font facade, and adding
  exact effective-alpha plus in-quad zero-coverage pixel oracles.
- candidate-matrix audit: Spark traced the registry, category assignments,
  corpus scenario, generated-manual draft, and SPipe promotion contract. No
  matrix cell can move from `unavailable` without an executable bound Pure
  Simple shaping/corpus run; `FontRasterizer` codepoint/layout diagnostics are
  insufficient. The scenario now prepares exact applicable `CORPUS.sdn`
  codepoint/raster witnesses for all 16 candidates, including Bengali rank 11
  and Noto Emoji `U+1F600`; the stale SC/French fallback was corrected. All
  statuses remain 0 `native`, 0 `fallback`, 26 `not-designed-for-script`, and
  74 `unavailable`. No Simple command ran because the session cap was exhausted.
- format-policy implementation: the neutral `common.encoding.sfnt` owner now
  validates bounded/nonoverlapping directories, required TrueType tables,
  excluded color/SVG/strike/CFF tables, signed 16.16 values, strict `fvar`
  defaults, while separate manifest helpers compare exact table/default-axis
  metadata. Both native loader owners preflight before native state mutation,
  including direct `FontRasterizer.load`; an independent raw replay accepted
  all 16 pinned binaries and exact records. Loader bool/nil APIs intentionally
  discard typed reasons. Pure Simple compound outlines for 14 faces and
  executable Simple evidence remain open, so REQ-008 is not complete.
- format-gate review: Spark independently matched all 16 table/default-axis
  records and reviewed aligned negative fixtures; the high-capability reviewer
  accepted the neutral dependency direction, both root loader guards, typed
  scenario diagnostics, and documentation scope. Static review PASS; no Simple
  command ran under the exhausted session cap.
- compound-glyf audit: raw inspection found 7,594 compound glyphs and 16,194
  components across 14 candidates (no cycles/malformed records, max 33 direct
  components, depth 2). Exact CORPUS mappings touch 76 compound roots/124
  components, all XY-positioned, depth 1, and at most two components. High
  review rejected implementing the unused offset-only stub: the current simple
  decoder is not glyph-slice bounded, reconstructs repeated-flag consumption
  incorrectly, mishandles off-curve contour starts, and discards original point
  numbering required for point attachment. Future Pure Simple work must add one
  glyph-ID/head+loca+maxp API, preserve explicit points, and bound recursion;
  native production rasterizers already own current compound rendering. No
  source/parser acceptance claim was added.
- shaping-metadata slice: selected Latin-1 witnesses now remain in one Latin
  run, Bengali rank-11 has explicit script identity, and mixed-script runs no
  longer overlap their starting X coordinate. `ShapedGlyph` carries absolute
  source/cluster identity plus current advances/zero offsets through Arabic,
  provisional Devanagari, and Thai reorder/grouping; `ShapedRun` carries trimmed
  caller language (`und` default) and explicit incomplete GSUB/GPOS flags.
  Bound cmap parity can produce render-valid material only for Latin, Cyrillic,
  Han, or a single emoji codepoint. Arabic/Urdu/Devanagari/Bengali/Thai and emoji
  sequences fail closed. Exact CORPUS metadata fixtures were added, but no
  matrix cell moved and no Simple command ran under the exhausted cap.
- shaping-metadata review: both Spark lanes verified all 12 exact CORPUS
  sequences, reordered source/cluster identity, mixed-run continuity, Thai
  grouping, and the whole-input single-emoji guard. High-capability review
  accepted source/tests/guide/SPipe scope. Static review PASS; executable Simple
  evidence remains unrun and REQ-007 stays open.
- final high-capability static review: PASS after correcting Noto Emoji's
  embedded full name to `Noto Emoji`, adding an exact SSpec assertion, and
  relabeling Bengali rank-11 evidence as candidate rather than fallback
  coverage. No Simple command was run.
- portable font artifact integration: three Spark audits independently found
  that font source emission was test-only, OpenCL bypassed the compiler artifact
  contract, WGSL concatenation would collide at bindings 0-2, and the native
  readback spec remains missing. Higher-model design review selected separate
  optimization/font companion artifacts per portable target. The shared backend
  planner now emits stable pairs with `_font_atlas` paths, exact font-symbol
  evidence, and explicit operation aliases; unit/system evidence checks pair
  ordering and WGSL isolation. Vulkan, toolchain execution, device submission,
  readback, and 3D GPU execution remain unclaimed. No Simple command ran because
  the session cap was already exhausted.
- portable font artifact final review: Spark re-review passed pair ordering,
  exports, WGSL isolation, and token-exact symbol rejection (including a
  suffixed near miss). Higher-model re-review passed source, tests, and the
  manually synchronized 30-scenario unit manual. Static review PASS; executable
  Simple/docgen and device evidence remain unrun.
- OpenCL dirty-atlas slice: Spark traced `FontRenderBatch.dirty_rects` through
  Engine2D and found every changed generation still transferred the full 4 MiB
  atlas. Higher-model review selected one offset-aware sibling of the existing
  OpenCL write primitive. Consecutive generations now upload validated dirty
  rows only; allocation, invalidation, gaps, empty/invalid metadata, and failed
  partial writes invalidate the generation so the next attempt full-uploads.
  An unconditional decision check distinguishes 4 dirty bytes from allocation,
  gap, invalid, and empty full-upload cases; conditional device coverage checks
  that old and newly uploaded glyph pixels both survive. This is static
  implementation evidence only; no Simple/native throughput claim was made.
- OpenCL dirty-atlas review: both Spark lanes and the higher-capability reviewer
  passed the unconditional upload decision, C bounds/pointer math, generation
  recovery, Rust/SFFI registration, conditional device oracle, guide/SPipe
  wording, and manually synchronized 9/8-scenario unit manuals. C syntax and
  Rust formatting checks passed; executable Simple/docgen remains unrun.
- coverage policy resolver: Spark compared real CUDA/Metal runtime integration
  with language acceptance; higher review rejected both backend slices without
  hardware execution and reduced registry work to one exact fail-closed lookup.
  `selected_font_coverage_cell` returns the canonical matrix cell or `nil` for
  unknown axes. It does not turn witness metadata into a loadable face and does
  not change the 0 native / 0 fallback matrix.
- coverage resolver review: both Spark lanes and the higher-capability reviewer
  passed exact optional lookup syntax, status-first witness gating, four focused
  assertions, unchanged 0/0/26/74 counts, guide/SPipe wording, and the manually
  synchronized five-scenario unit manual. Static PASS; Simple/docgen unrun.
- CUDA font runtime slice: higher review froze one bounds-checked PTX companion
  in the existing single CUDA module, a 15-slot/120-byte pointer ABI, persistent
  device atlas generation, typed Engine2D routing, and synchronized-prefix
  mirror parity. Three Spark lanes implemented PTX, ABI, and backend/Engine
  wiring; the existing atlas alpha extractor moved to the shared text helper
  with its Engine compatibility wrapper retained. CUDA full-uploads changed
  atlas generations; compiler CUDA C emission remains separate planning source.
  No CUDA device or Simple command ran, so runtime correctness is not promoted.
- CUDA runtime review: the extracted PTX companion assembled successfully with
  CUDA 13 `ptxas` for `sm_75`; C runtime syntax and Rust formatting checks also
  passed. Both Spark re-reviews and the higher-capability re-review passed the
  private 2×u64+13×s64 ABI, i64 framebuffer bound, atlas lifecycle, per-quad
  synchronization/mirror prefix, typed routing, 14-scenario manual, and strict
  claim boundary. CUDA device execution remains pending.
- Metal font runtime slice: two Spark audits and higher review froze exact
  common MSL reuse, an optional MetalSession-owned library/pipeline, the existing
  leak-free `rt_metal_run_compute_frame` seam, a 13-word/52-byte ABI, persistent
  full-upload atlas generation, prefix mirror coherence, and native-only typed
  Engine2D routing. Three Spark lanes implemented source, session/SFFI, and
  backend/Engine pieces; a convergence refactor removed duplicate backend
  shader/pipeline ownership and manual command encoding. No macOS Metal or
  Simple command ran, so native correctness is not promoted.
- sfnt manifest-name replay: the manifest corrects Noto Emoji's embedded full
  name to `Noto Emoji Regular` and the executable scenario compares all five
  pinned identity fields against all 16 real binaries. This is asset-identity
  replay only; runtime enforcement, candidate acceptance, and 0/0/26/74
  coverage promotion remain unchanged. Static checks only; Simple/docgen unrun.
- Vulkan font source export: `emit_vulkan_font_atlas_composite_source()` returns
  the canonical common GLSL 450 text unchanged for dedicated GLSL-to-SPIR-V
  compilation. Vulkan remains outside `PortableComputeTarget`; no compilation,
  submission, readback, or execution is claimed. The focused scenario checks
  the exact 15-input ABI: two buffer bindings and the contiguous 13-field
  parameter block.
- Vulkan font artifact plan: the dedicated plan preserves canonical GLSL,
  `main`, tool/format metadata, and `.comp`/`.spv` suffixes. Synthetic evidence
  covers pass plus every fail-closed reason, but contract validity is not
  compilation/execution and no compiled artifact exists without real capture.
- skill freshness: the guide now names `$sp_dev` as process owner for bundled
  fonts, shaping, glyph material, and GPU text; no source, test, or manual was
  regenerated for this documentation-only slice.
- loader selected-byte handoff: both native roots load exact selected bundled
  paths from owned verified/prevalidated bytes. Aliases and unmanaged fonts
  retain legacy path loading and are outside the race-free claim. The Pure
  Simple SHA `[u8]` to `[i64]` conversion amplifies memory for candidates up to
  25 MiB and must be replaced or measured before promotion. No matrix promotion.
- partial REQ-009: selected checksum/default-axis identity fences the whole
  glyph cache and atlas and is exposed in stats. Revocable generation-bound
  wrappers protect the process-global face and stale operations fail closed.
  Conditional real-dylib A-to-B evidence/manual remains unexecuted under the
  session cap. Full config/backend/program keys and concurrent multi-face
  ownership remain out of scope; no matrix promotion.
- font program-version fence: every batch stamps version 1 for
  `simple_font_atlas_composite_v1_u32`. CUDA/Metal/OpenCL reject mismatches
  before mutation and Engine2D replays CPU from quad 0. Conditional CUDA and
  OpenCL scenarios cover reject-then-v1 recovery; Metal remains static-only
  because no injectable dispatch seam exists. No execution promotion or full
  REQ-009 claim follows.
