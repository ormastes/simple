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
- Manual flows: `step("Load the pinned multilingual font manifest")`,
  `step("Accept exact-face-bound simple-script shaping")`,
  `step("Prepare one shared font batch for 2D and 3D")`,
  `step("Emit the selected font composite program and plan compilation")`, and
  `step("Prove native submission and device readback")`.
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
- Shared configuration owner: immutable `FontRenderConfig` and
  `FontExecutionPolicy` in `text_layout/font_types.spl`. The configured
  `FontRenderer` entrypoints are `prepare_text_configured`,
  `prepare_text_with_advances_configured`, `prepare_glyph_run_configured`, and
  `prepare_selected_glyph_run_configured`; compatibility methods construct the
  documented defaults and delegate.
- Minimum new material values: `FontRenderQuad` and `FontRenderBatch` in
  `text_layout/font_types.spl`; `FontRenderer.prepare_text(content, color,
  font_size) -> FontRenderBatch` reuses `render_text_payload` and cache
  generation rather than adding another renderer/cache.
- Existing emitter extension:
  `emit_portable_font_atlas_composite_kernel(target) -> PortableComputeArtifact`;
  no `GpuFontEmitter` class.
- Existing Engine2D entrypoints remain compatibility adapters. Configured text,
  advances, and shaped entrypoints return `bool`; `FontRenderBatch` carries
  config identity, execution target, and policy. Engine2D supplies
  `cuda, metal, opencl, vulkan, cpu`; Engine3D supplies `vulkan, cpu`.
  `Suggested(auto)` uses that order; Preferred/Required require a concrete
  supported target and unknown targets reject before mutation.
  Minimal Engine3D additions are
  `draw_text_hud(x: i32, y: i32, text_val: text, color: u32, font_size: i32)
  -> bool` and `draw_text_world(x: f32, y: f32, z: f32, text_val: text,
  color: u32, font_size: i32) -> bool`, plus matching `load_font`/`unload_font`;
  both consume the same batch. World coordinates project through the stored
  view/projection matrices; CPU is fallback evidence, never native promotion.
- Frozen manual steps: `step("Load the pinned multilingual font manifest")`,
  `step("Accept exact-face-bound simple-script shaping")`,
  `step("Prepare one shared font batch for 2D and 3D")`,
  `step("Emit the selected font composite program and plan compilation")`, and
  `step("Prove native submission and device readback")`.
- Setup/checkers: `setup_shared_font_fixture`, `expect_font_license`,
  `expect_language_coverage`, `expect_shared_font_batch`,
  `expect_backend_emission`, and `expect_font_render_parity`.
- Any unavailable helper fails with `assert(false)`/`fail(...)`; no silent
  placeholder or environment-only success is accepted.

## Phase

REQ-011 canonical routing and REQ-015 runtime configuration are implemented in
source; canonical execution is pending. Direct `arch/*/wm_entry.spl` demos are
explicitly compatibility-only and are not release blockers. Self-hosted
execution, canonical docgen, native Engine3D promotion, retained SimpleOS
pixels, and performance evidence remain release-blocking.

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
- Vulkan3D implementation review: the new font pipeline remains unpromoted.
  Graphics commands now use the canonical graphics pool/queue, device-local
  device selection now prefers one graphics+compute queue and uses it for
  staging, with a transfer-write visibility barrier. Uploads fail closed, each
  recorded draw owns immutable transient vertices, unknown completion retains
  resources until device idle, active recording is discarded on shutdown, and
  source-over alpha uses the matching destination-alpha factor. Selected-device
  evidence now comes from the actual borrowed device. Vulkan runtime/compiler
  checks and focused Rust contracts pass. The font target still does not share the
  CPU scene depth/color target, so device parity and world occlusion stay
  unavailable until a retained native readback witness proves them.
- current compiler gate: `sfnt_glyf.spl` was exactly localized to
  cast-type/generic ambiguity at spaced `<` comparisons. Generic angle brackets
  now require adjacency, the minimized/full-file parser regression passes, and
  bootstrap parentheses let stage2 complete discovery/codegen. The full CLI
  build now stops at link configuration because its core bundle omits hosted
  externs; the next bounded build must select `--runtime-bundle rust-hosted`.
  The misleading 10.1 GiB stage-3 event was bootstrap command misdispatch,
  not an Arabic parser leak; the dispatcher now gates on literal
  `native-build`. No fourth unchanged full build is permitted in this session.
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
- selected-asset hashing: the shared registry validator now computes SHA-256
  directly from bounded `[u8]` storage after the byte-length gate and before
  font parsing. Callers cannot supply a candidate digest. `spl_fonts` retains
  the native verified-bytes digest recheck as defense in depth. This does not
  promote any coverage cell.
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
- Batch identity evidence: every synthetic batch constructor supplies explicit
  identity/generation; system evidence snapshots cold/warm selected identity,
  empty/invalid preparation, and supplied glyph-run generation without
  claiming native availability. Native capture reads generation twice around
  identity, returns neutral `(0, "")` when stale, and discards material if the
  snapshot changes during preparation; no atomic/global-lock claim is made.
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
  retain legacy path loading and are outside the race-free claim. Pure Simple
  hashes selected `[u8]` payloads in bounded blocks, and the primary native
  renderer independently rechecks the expected digest. No matrix promotion.
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
- atlas dependency tokens: under serialized renderer access, renderer atlases
  use positive process-unique sequential tokens rather than renderer-local
  counters. Sequential distinct-renderer unit evidence prevents CUDA/Metal
  cache aliasing, and OpenCL token gaps select a full upload rather than dirty
  subrects. Concurrent token allocation and renderer ownership remain
  unsupported. Tokens carry no cross-process or temporal meaning; this does
  not complete REQ-009 or promote hardware evidence.
- compound corpus replay: the manifest scenario independently scans the pinned
  sfnt tables, confirms 14 compound-bearing faces and exact CORPUS totals of 76
  roots/124 direct components, and requires a nonempty Pure Simple outline for
  every mapped compound root. Native rasterizers stay the production owner;
  execution and the 0/0/26/74 matrix remain unchanged.
- selected outline fallback: the typed native wrapper retains already
  validated selected bytes and routes only a current selected face's native
  zero-handle miss through neutral common cmap/glyf rasterization. Negative
  errors, native successes, unmanaged/CFF paths, missing mappings, stale
  wrappers, and malformed native handles do not enter the fallback; close
  clears the retained bytes and rasterization performs no file I/O. Source
  contracts cover routing/ownership, but no fake native-miss injection or
  matrix promotion is claimed.
- compositional miss evidence: selected faces resolve the FreeType-only ABI,
  whose focused test forces a zero native result while the unchanged legacy
  ABI succeeds. Independent common sfnt raster assertions cover the second
  half; unmanaged faces keep the legacy ABI. No matrix promotion.
- Vulkan Engine2D font batch slice: the real canonical `vulkan` constructor is
  session-backed and accepts bounded precompiled font SPIR-V; the common
  three-buffer/52-byte ABI now has validated atlas upload, per-quad dispatch,
  synchronous completion, direct framebuffer readback, and an independent CPU
  parity oracle. All deterministic validation precedes cache/device mutation.
  Ordinary unavailable states replay CPU from quad zero; unknowable command,
  rollback, descriptor, or cleanup states poison the Vulkan surface into
  software without retrying unsafe resources. Conditional evidence remains
  unrun here, explicit fence/device identity is unavailable, and
  `promotion_ready` stays false.
- simple shaping acceptance execution: `bin/release/simple test
  test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl
  --mode=interpreter` completed with exit status 0 and no stdout. The source
  contains four scenarios; no passed-case count is inferred. Exact live-face,
  cmap/runtime ID, hmtx advance, material, missing/stale, and Chinese Mono-to-SC
  fallback checks establish the 54 identity rows, the Chinese mono fallback,
  exact Hindi, and the bounded Arabic/Urdu runs. At that execution the catalog
  remained 55 `native`, 1 `fallback`, 26 `not-designed-for-script`, and 18
  `unavailable` cells.
  This changes no GPU/native-execution claim; Vulkan promotion remains false
  and native Engine3D evidence remains pending.
- post-promotion registry gates: `bin/release/simple test
  test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl
  --mode=interpreter` and `bin/release/simple test
  test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
  --mode=interpreter` each completed with exit status 0 and no stdout. No
  passed-case count is inferred. The unit gate supports exact registry mapping,
  totals, and accepted-family metadata; the system command is the manifest
  manual's recorded run. Those historical passes preserve 55/1/26/18 and do
  not satisfy general complex shaping, native GPU readback, or Engine3D promotion.
- bounded Arabic/Urdu catalog promotion (2026-07-13): the already-passing exact
  Noto Sans Arabic witnesses for `ar` and `ur` are now accepted tuples. The
  source matrix is 57 native, 1 fallback, 26 not-designed, and 16 unavailable;
  its focused manifest/shaping rerun remains pending on the rebuilt full CLI.
  Marked Arabic, general BiDi/GSUB/GPOS, and unselected Indic sequences remain
  fail-closed and are not promoted.
- fenced Vulkan promotion correction (2026-07-13): the canonical Engine2D
  Vulkan lane now records a stable selected accelerated device type plus
  device/driver identity, uses a real wait-and-destroy fence, requires direct
  device readback and the absolute CPU oracle, and poisons the surface when
  completion becomes unknown. CPU/other devices and unfenced submission stop
  before font batch, atlas, or destination mutation. The focused frozen flow is
  `step("Prove native submission and device readback")` in
  `test/02_integration/rendering/vulkan_font_composite_classification_spec.spl`,
  mirrored at
  `doc/06_spec/02_integration/rendering/vulkan_font_composite_classification_spec.md`.
  Automatic docgen and execution are not claimed: the deployed self-hosted
  compiler exits 139 on the new Vulkan extern surface, while rebuilding the
  Rust compiler is blocked by missing vendored `vendor/rspirv/dr/build.rs`.
  Engine3D REQ-012/REQ-013 and native performance NFRs remain open.
- REQ-008 source completion (2026-07-13): the neutral sfnt owner rejects legacy
  `bdat`/`bloc` strikes with the existing unsupported-table policy and exposes
  `validate_glyf_font_instance`, which accepts only `static` or the exact
  declared default-axis tuple. The selected registry reuses that owner before
  native loading. Focused checks repeat the pinned Pixelify Sans `wght=400`
  Pure Simple raster and pin the existing 8×16 VGA `A` glyph checksum without
  adding a rasterizer or asset. One interpreter attempt for each of
  `sfnt_spec.spl`, `sfnt_glyf_spec.spl`, and
  `bitmap_font_gpu_offload_spec.spl` exited 139 with no stdout due to the
  deployed compiler blocker; no retry or runtime PASS is claimed. Non-default
  `gvar` interpolation and broader legal compound component modes remain excluded.
- WebRender-IR/Draw-IR font family bridge (2026-07-13): canonical web style now
  preserves default, inherited, overridden, and shorthand `font-family` in
  Draw IR computed style. The Draw IR schema remains unchanged. Engine2D keeps
  the legacy bitmap route because web layout still uses fixed 5×7 metrics;
  selecting TTF only at paint would create layout divergence. Focused
  source/unit contracts were added but not executed due
  to the deployed compiler exit-139 blocker. The production web pixel painter
  still bypasses Draw IR, and SimpleOS has no shared immutable-data image
  manifest or Pure Simple selected-face startup load; neither is claimed done.
  One interpreter attempt each for `simple_web_renderer_spec.spl`,
  `draw_ir_adv_spec.spl`, and `font_renderer_spec.spl` exited 139 with no
  stdout; the no-retry guard was honored and no runtime PASS is inferred.
  Higher integration review passed after paint-time family selection was removed
  and REQ-008 was reduced to honest partial status. The touched web renderer's
  pre-existing raw environment read was also moved to the canonical env facade;
  `direct-env-runtime-guard --working` then passed.

- bootstrap evidence update (2026-07-13): the narrow stage-4 full-CLI hosted
  runtime authorization mismatch is fixed and its Rust regression test passes.
  Fresh seed and hosted archive builds succeeded. A refreshed parser then found
  reserved `function` locals in MIR lowering; they were renamed to
  `hir_function`. The next stage-2 build cleared parsing but timed out at the
  bounded 600-second cap without an artifact. No third retry is made. Therefore
  the focused font/SPipe commands remain pending, and no additional runtime,
  native GPU, SimpleOS pixel, Engine3D, or performance PASS is claimed.

- entry-closure performance evidence (2026-07-13): a 25-second syscall profile
  observed 552,708 `statx` calls in repeated numbered-layer module resolution.
  A cache experiment reduced one short sample by ~12%, but higher review found
  broken narrow-root `crate.*` semantics and unsafe cross-thread invalidation;
  it was reverted. The cache-preserving stage-2 build still timed out at 600
  seconds without an artifact, so no full-CLI or downstream font execution
  evidence is claimed.

- legacy producer route evidence (2026-07-13): a reviewed SSpec now constructs
  real Web, GUI-widget, and WM compositions, requires exactly one requested text
  command, validates its pinned identity and serialized advance count/values/
  width sum, then submits the whole composition through the shared Engine2D CPU
  Draw IR executor. The companion manual deliberately claims only structural
  metadata retention and canonical routing: the executor does not consume the
  serialized advances, and glyph pixels/pixel parity remain unproved. Execution
  and canonical docgen are pending on the full self-hosted CLI blocker above.

- objective audit follow-up (2026-07-13): all 16 pinned TTF files were compared
  with their manifest stat sizes and SHA-256 values; zero mismatches were found
  and the total remains 51,764,704 bytes. Stale 10/6 documentation was corrected
  to 11 accepted/5 candidate faces, exact Arabic/Urdu witness scope was aligned,
  and the emission manual now includes its existing Vulkan source/ABI/plan
  contract. A guaranteed stale system assertion for matrix cell 10 was corrected
  from unavailable to native Noto Sans SC. Portable compute artifacts now own
  deterministic source/version SHA-256 methods used by the emission SSpec.
  Focused Rust-seed `test` and `check` diagnostics could not enter the Simple
  runner (`Permission denied` source runner and missing delegated `bin/simple`),
  so they provide no PASS. The self-hosted CLI, native GPU, retained SimpleOS
  pixels, Engine3D promotion, and performance gates remain open.

- REQ-009 cache-identity slice (2026-07-13): `FontRenderBatch` now derives a
  length-delimited atlas owner from program version, live checksum/default-axis
  identity, face generation, and dimensions, with dependency generation added
  for the complete upload-cache identity. CUDA, OpenCL, Metal, and Vulkan2D
  reuse atlas uploads only when owner and generation both match; failure and
  teardown clear both. Atlas generation allocation now uses the existing real
  AtomicI64 compare-exchange primitive, eliminating cross-renderer token
  collisions until fail-closed exhaustion. Resolved layout metrics include the
  live face identity, use a mutex-protected 128-entry ring, and bypass caching
  above the documented family/content limits. High review passed; focused diff
  and direct-env working/staged audits pass. Runtime specs remain unexecuted
  because the self-hosted CLI blocker is unchanged. Transform/scale,
  device-feature, and emitted-program artifact identity keep REQ-009 partial.

- Exact emoji candidate gate (2026-07-13): the shaping source now permits
  identity completion only for the single U+1F600 scalar rendered by the
  pinned bundled Noto Emoji path. Unit and SPipe sources require a valid
  `FontGlyphRun`/`FontRenderBatch`, the live face generation, one quad, and
  nonzero atlas pixels across all ten selected language tags; other emoji,
  repeated emoji, variation-selector, modifier, ZWJ, and impostor-path cases
  remain fail-closed. Focused diff checks and high review pass. Registry and
  matrix status intentionally remain unchanged pending execution by the
  self-hosted runtime; this is not runtime PASS or promotion evidence.

- REQ-009 scale/artifact-plan slice (2026-07-13): canonical raster scale was
  confirmed to be `font_size`, already present in glyph, atlas-entry, and
  resolved-metrics keys; focused source tests now require cold material for a
  changed size and warm reuse at each size. Translation remains late-bound and
  does not invalidate atlas uploads; other CTM components remain unsupported.
  `PortableComputeCompilePlan` now carries the emitted artifact version hash,
  rejects an empty identity, and preserves it through invocation, evidence,
  and result records. Source mutation produces a distinct identity. Focused
  diff/placeholder checks and high review pass. Runtime device/pipeline cache
  identity, self-hosted execution, and promotion evidence remain open.

- REQ-009 runtime identity slice (2026-07-13): VulkanSession's one-entry font
  pipeline cache now binds reuse to a mode-prefixed SHA-256 of the exact SPIR-V
  bytes or frozen GLSL source and rejects a different valid artifact without
  touching retained handles. CUDA, OpenCL, and Vulkan atlas uploads are bound
  to one backend session: active replacement, including invalid replacement
  input, fails before validation or retain and preserves atlas state and both
  reference counts. Fresh Vulkan initialization now rejects invalid dimensions.
  Behavioral unit sources, synchronized manuals, focused diff/placeholder
  checks, direct-env working/staged audits, and high review pass. No self-hosted
  execution or native-device promotion is claimed.

- Self-hosted CLI recovery audit (2026-07-13): no retained ELF can safely run
  the focused specs. `font-fix/full` contains unresolved CLI stubs, stage3 is a
  bootstrap-only dispatcher with known command misrouting, and all mini runner
  candidates either delegate to the Rust seed or bypass required SPipe
  preprocessing. Preserve `build/bootstrap/font-verify2/native_cache`; the next
  build session must first fix/prove the module-resolution compile-time path,
  then make one fresh cache-backed stage2/full attempt and require direct
  `check` plus `test --list` before deployment. No old artifact is promoted.

- SimpleOS pre-QEMU compiler fix (2026-07-13): the retained WM evidence failed
  before QEMU because IRDSL parser/validator sources contained desugaring
  leftovers compiled as unresolved calls. The parser and validator now use
  canonical text/array methods and direct mutable receiver calls; a focused
  parse/validate/coverage/codegen spec covers multi-parameter splitting,
  validator error accumulation, and empty coverage without division by zero.
  Static and high review pass. The retained compiler still exits 139 in check,
  so no build, QEMU, or pixel promotion is claimed.

- Engine3D atlas identity fix (2026-07-13): Vulkan 3D atlas reuse now requires
  both `FontRenderBatch.atlas_owner_identity()` and dependency generation.
  Texture replacement, failed upload, and shutdown invalidate owner/generation;
  shutdown also clears the texture handle and dimensions. A pure unit predicate
  covers warm reuse, generation change, a real second batch owner, and invalid
  state. Small-agent and high review pass; native depth/readback promotion
  remains open.

- Durable font performance evidence contract (2026-07-13): the perf SSpec is
  now the sole collector and overwrites a source/font-pinned `evidence.env`;
  the native system promotion spec only loads it. One shared helper owns the
  complete evidence type, overflow-bounded budget gate, exact 11-sample p95
  validation, strict ordered parser, and stale collector/helper/renderer/backend
  source rejection. A focused unit source rejects
  duplicate, malformed bool, short samples, p95 tampering, and stale font or
  collector identities. Runtime execution remains blocked by the unchanged
  self-hosted CLI failure, so NFR-004/005/006 are not promoted.

- Engine3D device-readback provenance (2026-07-13): Vulkan 3D device evidence
  now binds the submitted graphics command and completed fence to the exact
  native color-image handle and `width*height*4` payload. Frame start clears
  prior target/readback authority. The system gate rejects CPU devices, missing
  driver identity, fallback source labels, wrong byte counts, and any mismatch
  between native RGBA8 evidence and public Engine3D pixels. Direct-env audits
  pass. Native execution and real world-depth occlusion remain open.

- Engine3D world-depth source fix (2026-07-13): the Rust Vulkan world-font
  pipeline now tests and writes depth. The shared fragment shader discards
  zero-coverage atlas texels; its regenerated 1,180-byte SPIR-V validates and
  is hash-pinned. The system gate replaces scalar range self-attestation with
  near-only/far-only/both-order device frames under a translated perspective
  camera and checks every fully opaque overlap pixel for near-wins behavior.
  Focused Rust unit, shader validation, and direct-env audits pass; native
  execution remains blocked by the self-hosted CLI lane.

- Engine3D resource/HUD evidence tightening (2026-07-13): adapter readiness and
  evidence now resolve exact logical pipeline/texture IDs to native handles;
  positional resource-array assumptions are removed and hit/miss mappings are
  unit-pinned. A HUD-only native frame derives exact nonzero pixel count and
  bounds from the canonical `FontRenderBatch` atlas at `(4,4)` and compares
  device readback before the mixed HUD/world parity frame. Small-agent review
  passes; native execution remains blocked by the self-hosted CLI lane.

- GPU plan/promotion hardening (2026-07-13): the portable CUDA compile command
  now uses the real `nvcc --ptx -o <output> <source>` syntax; a local NVCC 13
  smoke produced PTX. Engine2D Vulkan can promote only a validated
  `precompiled-spirv` pipeline. Runtime GLSL remains diagnostic and returns
  `executed-unpromoted`/`precompiled-spirv-required` even after successful
  fence, readback, and parity. Requirements, research addenda, architecture,
  design, guide, six-SSpec plan, manuals, and Codex/Claude SPipe rules now use
  the same WebIR/DrawIR/Engine2D/SimpleOS/Vulkan claim boundary. Static guards
  pass; self-hosted execution and canonical docgen remain blocked.

- Self-hosted Stage-17 rejection (2026-07-13): candidate SHA-256
  `9edef224333953a8970079e20cfda633c39e91c4cc16ad5fbb44504c67a4364f`
  defines `rt_path_join`, but was built from dirty `90f92f32ed12` sources with
  no acceptance log. Its sole focused check of `font_sffi.spl` mis-tokenized
  ordinary `=`, `>`, and `+` operators as malformed integer literals. Stages
  15–17 are rejected as verification runtimes; no sibling retry or PASS claim
  is permitted before an accepted pure-Simple replacement parses this source.

- Engine2D precompiled Vulkan font artifact (2026-07-13): Android NDK `glslc`
  compiled the canonical 2,796-byte Simple GLSL source to a 10,772-byte SPIR-V
  module; `spirv-val --target-env vulkan1.1` passed and reflection shows `main`,
  local size 64, and bindings 0/1/2. The retained session now auto-installs the
  embedded SHA-256 `e25d25b8157fc2554822637603471a442f678eb58e20da167bfb023d7577880a`.
  Native fence/readback/parity evidence remains pending an accepted compiler.

- SimpleOS direct FAT32 font staging (2026-07-13): the host builder validates
  the pinned Noto Sans Mono length/SHA with portable SHA tooling, requires the
  asset even when invoked directly, and creates `/SYS/FONTS/NOTOSANS.TTF`.
  Both Simple VFS implementations now read through the existing 4 MiB ceiling
  instead of truncating at 1 MiB. A read-only FAT32 parser recovered 1,708,408
  bytes from a disposable image with SHA-256
  `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
  This proves image packaging only; QEMU guest pixels remain unavailable.

- Self-hosted Stage-21 rejection (2026-07-13): new candidate SHA-256
  `97d4b1b5f43bc0a59be8c6884c43925e52cc8eba33db987387903e7672043f6e`
  is a 33,992,392-byte ELF built from dirty `90f92f32ed12` sources without an
  acceptance log. Its sole 90-second focused check of `font_sffi.spl` repeated
  Stage-17's malformed-integer errors on ordinary `=`, `>`, and `+` tokens.
  Stage 21 is rejected; no canonical self-hosted test, docgen, QEMU pixel,
  native GPU, or performance PASS is claimed.

- Clean-cache Stage-23 rejection (2026-07-13): a fresh Rust-seed bootstrap
  compiled 1,041 objects with 0 cached/0 failed and produced the pure-Simple
  candidate SHA-256
  `83d7680c8b718824c1024ee0089e8c6011e541944dc9ddd181c345200d0ce4e8`.
  Its first minimal native probe failed MIR lowering with `undefined variable:
  value` for `identity(value)`, proving the current `rt_is_none` guard drops a
  non-optional `HirParam.symbol`. The next bounded fix is to use
  `parameter_symbol.id` without an optional/nil guard, then start a new session
  with a new cache. No font/runtime promotion or GitHub push is claimed.

- Clean-cache Stage-29 rejection (2026-07-13): after fixing non-optional
  `HirParam`/`NamedVar` SymbolId handling, removing the dead post-scope lookup,
  typing `incremental_parse_file` as `Result<SdnValue, text>`, and adding
  explicit `BuildCache.load` branch returns, a fresh 1,041-object/0-cache build
  produced SHA-256
  `8f8e32d86b5ac3ab95dcfafafff56ab8b9f744c4062bc512c6da2ec4629f5a3d`.
  Its first unchanged `identity(1)` native probe still trapped with
  `field access on nil receiver` (exit 132). The three-cycle cap is exhausted;
  no focused font check, deployment, verification PASS, or GitHub push is
  claimed in this continuation.

- Stage-29 layout root cause and bounded Stage-31 verification (2026-07-13):
  GDB proved `MirToLlvm` stored its valid builder at offset 0 while the split
  `impl MirTextCodegen for MirToLlvm` in `core_codegen.spl` loaded every field
  at +8 bytes. The split module now uses the canonical inherent
  `impl MirToLlvm`; its sole trait-default dependency, the no-op unsupported
  fallback, is an equivalent local `case _: ()`. Highest-capability review
  passed and the clean rebuild no longer crashes or emits the trait symbol.
  Final linking remains blocked because both supported runtime bundles omit
  `rt_path_parent`, `rt_mkdir_p`, and `danger`. The three-cycle cap is reached;
  no candidate promotion, verification PASS, or GitHub push is claimed.

- Bootstrap runtime-link root fix prepared (2026-07-13): the remaining six
  link errors came from legacy names/syntax, not missing new functionality.
  Reachable compiler code now reuses bundled `rt_dir_create_all` and the
  existing driver dirname helper. The bundled core stdlib's 67 legacy
  `danger:` blocks now resolve to one shared pure-Simple helper that executes
  their closure, preserving pointer-operation behavior without a weak stub.
  Static regression guards and `git diff --check` pass. A fresh build is
  deliberately deferred to the next bounded cycle; no verification PASS or
  GitHub push is claimed.

- Stage-34 strict hosted-link follow-up (2026-07-13): the authorized hosted
  bootstrap lane cleared the earlier runtime aliases and exposed only two
  trait-default `is_empty` calls, the missing native `rt_jit_cleanup` export,
  and the unresolved `danger` block helper. The two calls now use direct
  trait defaults are now added to both bootstrap HIR function accumulators,
  and `danger` is the pure-Simple closure helper above. High review rejected
  a cleanup-only native export because it lived outside the linked runtime;
  that attempt was removed. The remaining root task is splitting the native
  JIT manager from pure hotspot planning so bootstrap closure does not pull
  interpreter-only externs. Per the bounded-cycle rule, no further build or
  push is claimed in this continuation.

- Stage-35 strict candidate and probe (2026-07-13): the Rust bootstrap seed
  built the hosted bootstrap closure with 616 compiled, 0 cached, 0 failed;
  SHA-256 is `d57d0114b4353f78ffab1b5a126a377a9c4b092bae5ebaae9aaf1b7599858ed4`.
  Stage35 then strictly native-built the original one-module identity probe;
  the 22 KiB binary printed `1`, and its SHA-256 is
  `85651d8c6af6f07aec81598fb691eb354af0809a638e9a4b86aed3daca7be0f6`.
  High review passed the JIT policy/manager split after returning pure config
  factories to policy; both files pass focused bootstrap-seed checks. That
  final API-placement edit postdates Stage35, so Stage35 is diagnostic rather
  than source-exact.

- Stage-36 self-rebuild rejection (2026-07-13): Stage35 ignored the expected
  616-module entry closure, scanned unrelated application trees, and emitted
  body stub fallbacks despite `SIMPLE_NO_STUB_FALLBACK=1`. The run was stopped
  once the repeated unrelated-module pattern was clear. Stage35 is accepted
  only for focused native compilation evidence, not source-exact deployment;
  no font-suite verification PASS or GitHub push is claimed.

- Stage-37 source-exact strict candidate (2026-07-13): the Rust bootstrap seed
  built the reviewed hosted bootstrap closure from the current sources with
  616 compiled, 0 cached, and 0 failed. The 21,017 KiB candidate at
  `/tmp/simple-simd-aot-next/build/bootstrap-font-fresh-stage37/simple` has SHA-256
  `8966b499973e55e9bc49c2470f05b056659d7a2a2cebb18995564d0d331ae261`.
  It strictly native-built the unchanged identity probe (1 compiled, 0 cached,
  0 failed); the probe printed exactly `1` and retained SHA-256
  `85651d8c6af6f07aec81598fb691eb354af0809a638e9a4b86aed3daca7be0f6`.
  Its undefined-symbol table contains none of `danger`, `unsafe`,
  `rt_jit_cleanup`, trait-default `Len`/`ExactSizeIterator.is_empty`,
  `rt_mkdir_p`, or `rt_path_parent`. Stage37 is the accepted source-exact
  compiler candidate; focused font/runtime verification and isolated GitHub
  publication remain before completion.

- Stage-37 focused font verification result (2026-07-13): the broad
  single-file in-process route was stopped after it repeated the known
  entry-closure overreach and malformed-integer parser flood. The explicit
  entry-closure route did compile the existing Simple 2D vector-font probe.
  A canonical Cranelift Simple-core archive build passed, but final probe
  linking failed because that archive does not provide the hosted font/SFFI
  surface (`spl_wffi_call_i64`, `rt_font_*`, `rt_gui_get_glyph_8x16`, and
  related dynamic-loader helpers). The bounded verification cap is exhausted.
  STATUS remains FAIL; no commit, rebase, or GitHub push was performed.

- Stage-39/40 native font root recovery (2026-07-13): the pure-Simple runtime
  compiler now includes the existing `runtime_font.c` object, bitmap fallback
  reuses the shared Simple 5x7 glyph table instead of the interpreter-only
  `rt_gui_get_glyph_8x16`, and the two bootstrap-only generic `is_empty`
  link gaps use direct `len()` checks. Stage40 built source-exact with 616
  compiled, 0 cached, and 0 failed; its SHA-256 is
  `92e45a0b9309a6d04b11c89eb580f0327690ba2c39b9557428c385cef9036391`.
  Its single-file native-build path now
  preserves the entry through fixed bootstrap input fields and performs import
  discovery before enabling closure mode. The focused TTF probe stopped at
  three unresolved public-library aliases (`common.ui.glyph_bitmap_5x7`,
  `std.simd`, `std.encoding.simd_text_ffi`) before codegen; the resolver now
  carries the canonical runtime-family order and `common.*` alias, but that
  final resolver edit postdates Stage40. The bounded rebuild cap is reached;
  STATUS remains FAIL and no GitHub push is claimed.

- Stage-41/42/43 lexer recovery result (2026-07-13): Stage43 rebuilt the
  source-exact pure-Simple compiler with 616 compiled, 0 cached, and 0 failed.
  The one permitted focused native font probe still failed before font code
  execution while parsing `src/std/common/encoding/utf8.spl`: integer and
  punctuation token text was corrupted (examples include blank integer text,
  `.le`, and `by`), followed by a nil-receiver runtime error and exit 132.
  The direct-token lexer repair therefore lacks the required exact native token
  regression and is not accepted. The three-cycle cap is exhausted; STATUS
  remains FAIL, and no commit, rebase, or GitHub push was performed.

- Post-Stage43 root-cause repair (2026-07-13, not yet rebuilt): CoreLexer
  offsets are character indices while native text slicing is byte-indexed, so
  Unicode before a token shifted parser offset reconstruction (the observed
  em dash accounts for the two-byte drift from `128` to `= 1`). The active
  parser path now captures `lex_token_text()` immediately, preserves empty
  newline/indent/dedent/EOF text, and never reconstructs ordinary token text
  from offsets. The lexer getter likewise returns its captured direct text.
  A regression prepends a literal em dash and asserts the complete exact
  kind/text stream through EOF. Independent root review passes the
  implementation; verification awaits the next bounded source-exact rebuild,
  so STATUS remains FAIL and no GitHub push is claimed.

- Post-Stage43 completion audit and source corrections (2026-07-13, no rerun):
  static manifests remain internally exact (16 font binaries, 51,764,704
  bytes, pinned licenses/hashes; CLDR top ten plus rank-11 witness; 100 matrix
  cells = 57 native, 1 fallback, 26 not-designed, 16 unavailable). The audit
  found no accepted self-hosted PASS for the font/CLDR/SimpleOS specs and no
  native GPU, Engine3D, QEMU framebuffer, or NFR performance promotion.
  Canonical SPipe guidance now carries the frozen multilingual workflow; the
  main and cross-guides distinguish implemented source/oracles from execution.
  Pixelify source evidence pins 15x21, advance 19, and its raster SHA-256.
  Draw IR now skips and reports a failed nonempty font identity, preserves the
  prior face on lookup/load failure, and selected-face batch failure no longer
  silently reaches bitmap rendering. The empty `pass_do_nothing` renderer
  branch was simplified. Independent higher review passed these narrow source
  changes, but they are not executable evidence. STATUS remains FAIL; no
  commit, rebase, or GitHub push was performed.

- Top-ten performance fixture correction (2026-07-13, no rerun): the durable
  benchmark oracle now follows the pinned CLDR rank order and includes
  Indonesian (`id`, rank 10, `U+0049`) instead of Bengali (`bn`, rank 11,
  cutoff-only). The collector diagnostic, durable evidence schema, and focused
  unit assertion share the corrected ten-codepoint identity. This is a
  source-only correction; multi-face execution, native performance evidence,
  and STATUS remain pending/FAIL.

- Fresh-origin publication recovery (2026-07-13, no runtime rerun): the reviewed
  font lane was transplanted with three-way merges onto current `main@origin`,
  preserving upstream compiler, GPU, UI, WM, and SimpleOS work. Independent
  reviews resolved every merge conflict and restored one dropped Vulkan cache
  assertion. `FontRenderBatch` atlas ownership now directly includes face
  generation plus canonical rendering/transform identities; this narrows but
  does not complete REQ-009 because public CTM rejection, backend/device and
  non-Vulkan artifact keys, run caching, and full telemetry remain open.
  Static diff checks pass. The post-Stage43 compiler rebuild, focused specs,
  native/QEMU/performance evidence, verify PASS, commit, and push remain pending.

- Stage-44/45/46 fresh-origin compiler recovery (2026-07-13): three bounded,
  source-exact rebuild cycles reduced the final-link gaps and then produced the
  pure-Simple Stage46 compiler with 633 compiled, 0 cached, and 0 failed in
  192.0 seconds. The 21,858,064-byte binary has SHA-256
  `ffd99ac92542485a0ad5d5bb436c18fb627ec827233abea7a198137e30b5cb94`.
  The unchanged focused native font probe no longer crashed or reported
  malformed Unicode tokens, but stopped before parsing on the three public
  aliases `common.ui.glyph_bitmap_5x7`, `std.simd`, and
  `std.encoding.simd_text_ffi`. Independent history review confirmed that the
  recovered runtime-family/common-alias resolver hunk had been omitted from
  the fresh-origin transplant. That exact, narrowly reviewed source fix is now
  restored in `driver_source_loading.spl`, after the Stage46 binary was built;
  no environment-only correction can exercise it. The three-cycle cap is
  exhausted, so a later bounded session must rebuild once and rerun the same
  probe. STATUS remains FAIL; no commit, rebase, or GitHub push was performed.

- Stage-47/48/49 continuation (2026-07-13): Stage47 proved the recovered import
  resolver compiled but exposed one bootstrap-only `text.is_empty()` link gap
  in the Lean backend; the exact recovered `len() == 0` replacement was
  independently reviewed. Stage48 and Stage49 then rebuilt source-exact with
  633 compiled, 0 cached, and 0 failed. Stage49 took 167.0 seconds and produced
  a 21,369,352-byte binary with SHA-256
  `c3476cdd474c0c7738ab1640ce2869f0354c7a4769dcb8000bf1861b058e3de2`.
  The unchanged native TTF probe now resolves all three prior public-library
  aliases and reaches phase 2. It exposed a shared flat-AST bridge bug: decoded
  shader braces and the exact ASCII-table literal `{|}` were speculatively
  parsed as Simple interpolation expressions. Saving/clearing/restoring the
  parser error flag removed the false phase-2 fatal gate, but Stage49 still
  ended in an unlocalized nil-receiver crash after those speculative probes.
  Independent review recommends the minimal preflight now present in source:
  reject empty, delimiter-only, multiline, carriage-return, or semicolon-bearing
  brace bodies before entering the speculative parser. This avoids every
  observed false candidate and its parser/AST mutation, but it postdates the
  Stage49 binary and is not executable evidence. The three-cycle cap is
  exhausted. A later bounded session must rebuild once, rerun the unchanged
  probe, and classify any remaining nil crash independently. Broader completion
  also still requires REQ-009 lifecycle/cache keys, the true mixed top-ten
  multi-face performance workload, native Engine3D evidence, and a backend
  promoted end-to-end for both engines. STATUS remains FAIL; no commit, rebase,
  or GitHub push was performed.

- Stage-50/51/52 continuation (2026-07-13): Stage50 and Stage51 rebuilt the
  source-exact compiler with 633 compiled, 0 cached, and 0 failed. Stage50
  took 167.7 seconds; Stage51 took 164.3 seconds. The interpolation preflight
  cleared the prior false shader/ASCII brace candidates. A real font SFFI was
  built at `build/lib/libspl_fonts.so` (4,051,440 bytes, SHA-256
  `f3e237be1b624be5f41c5febfcfcda72d8397c0ec72b66ee6021de0c12769966`),
  and the pinned TTF is 1,708,408 bytes with SHA-256
  `2cb2adb...a081`. Stage51 reached LLVM object emission and native linking;
  independent history review identified the compiled `for` transport loss in
  `link_llvm_native`, while the hosted runtime also needed `runtime_font.c`.
  Source now uses typed indexed object transport, a fixed ordered 12-object
  runtime array containing both DirectX and font objects, and raw direct-LLD
  as-needed flags. The final Stage52 rebuild was correctly run without unsafe
  stub fallback and stopped after 49 existing full-tree critical compilation
  failures; the feature lane additionally exposed parse failures in
  `selected_arabic.spl` and `shaper.spl`. The three-cycle cap is exhausted.
  No Stage52 binary, native TTF execution, verify PASS, commit, rebase, or
  GitHub push exists. STATUS: FAIL.

- Stage-53/54 continuation (2026-07-13): the two feature parser failures were
  corrected, Draw IR now consumes producer-resolved advances through the one
  canonical `FontRenderer` while preserving native bearings/kerning, and the
  artificial fresh-device single-face restriction was removed. The new helper
  uses UTF-8 byte offsets with logarithmic lookup; whitespace-only batches stay
  valid and malformed metadata fails as `text-font-advances`. Stage53 rebuilt
  the current pure-Simple bootstrap compiler with safe stub fallback disabled:
  633 compiled, 0 cached, 0 failed, 174.7 seconds. The Engine3D Vulkan lane now
  has real graphics command submission, font texture binding, HUD/world
  pipelines, fence completion, device-image readback, and tested depth
  test/write state. Current Rust runtime check and three focused Vulkan font
  tests pass. The three-face top-ten performance collector now shapes the exact
  accepted witnesses into one shared atlas and measures identical CPU/Vulkan
  sequences; its durable schema is v2 and remains explicitly unavailable until
  isolated paired 2D/3D RSS evidence exists.

  Stage54 then used Stage53 (not the Rust seed) to compile all 1,000+ full-CLI
  modules against the freshly rebuilt native archive. Compilation completed,
  but the final link failed. The retained response file contains generated
  Simple objects and `libsimple_native_all_stripped.a` but no fresh C runtime
  archive, leaving owned symbols such as `rt_mkdir_p` and
  `rt_font_glyph_bitmap` unresolved. It also exposed existing native-project
  resolution gaps: some calls reference unmangled `run_check`/`json_serialize`
  while their definitions are mangled, and unsupported GPU extern modules enter
  the broad CLI closure without owned runtime definitions. This is the first
  bounded verification/fix cycle for this continuation. Native Simple specs,
  3D RSS, complex shaped Draw IR, verify PASS, commit, rebase, and push remain
  pending. STATUS: FAIL.

- Stage-55 bounded verification (2026-07-13): native-project archive
  composition was corrected and its focused Rust test proves that the composed
  archive owns both `rt_mkdir_p` and `rt_font_glyph_bitmap`; compiler `cargo
  check` also passes. The source lane now additionally carries semantic shaped
  glyph payloads through producers into Draw IR and the canonical transient
  `FontRenderer`, plus paired fresh-process 2D/3D RSS probes. A second
  self-hosted bootstrap refresh was deliberately terminated: despite
  `SIMPLE_NO_STUB_FALLBACK=1`, the older Stage53 compiler emitted
  `CODEGEN-STUB-FALLBACK` after a real verifier type mismatch in
  `ComponentStats.get_metric`. That output is unsafe and is not accepted as a
  compiler or verification artifact. The remaining broad CLI symbol-ownership
  problem is recorded in
  `doc/08_tracking/bug/stage54_hosted_entry_closure_symbol_ownership_2026-07-13.md`.
  Focused Rust/Vulkan/linker checks pass, but native Simple specs, pixel-oracle
  and performance evidence, production verify PASS, commit, rebase, and GitHub
  push do not exist. Under the bounded-cycle and no-push-before-PASS rules,
  synchronization remains gated. STATUS: FAIL.

  The final allowed focused check confirmed that Stage53 cannot parse this
  module independently: its parser rejects the existing `from ../...` imports
  before semantic/codegen checking. Therefore the later verifier mismatch
  cannot be repaired or validated as a font-lane source change with the current
  self-hosted artifact. The three-cycle cap is exhausted; no further rebuild or
  retry is permitted in this session.

- Documentation/process readiness audit (2026-07-13): refreshed the canonical
  test plan, architecture, detail design, feature guide, legacy route manual,
  and SimpleOS guide for the three-face performance/RSS collector, handle-free
  shaped Draw IR payload, serialized-advance consumption, GPU-source example,
  and guest font evidence path. `.claude/skills/spipe.md` and
  `.codex/skills/{sp_dev,system_test}/SKILL.md` carry the font-specific process
  contract. `.agents/skills/`, `.claude/agents/spipe/`, and `.gemini/commands/`
  are N/A because they contain no font-specific recipe or changed generic
  workflow contract; duplicating the canonical rule there would create a second
  authority. All six manuals still require canonical self-hosted execution and
  `spipe-docgen`; native Engine3D, SimpleOS pixel, and performance artifacts are
  still missing. Documentation readiness therefore remains `STATUS: FAIL`, and
  this update makes no PASS, commit, rebase, or push claim.

- Higher-model shaped-pixel review (2026-07-13): the producer/SDN/executor path
  is structurally unified, but `prepare_selected_glyph_run` currently places
  glyph bitmaps at shaped pen x/y without applying the rasterized glyph's
  horizontal bearing or converting its vertical bearing/baseline convention.
  The same omission exists in the older neutral glyph-run adapter. Existing
  checks assert IDs/metadata, not Arabic/Hindi baseline pixels, so changing the
  signs without an executable pixel oracle would be speculative. Add one exact
  shaped CPU pixel oracle first, then fix the shared placement once and reuse it
  for CPU/Vulkan readback. Runtime shader provenance is also incomplete: Simple
  emits canonical sources/plans, while CUDA still loads separate PTX and Vulkan
  loads externally generated pinned SPIR-V. STATUS: FAIL.

- Language-policy and interchange continuation (2026-07-13):
  `selected_font_asset_for_language_category` now maps only promoted sparse
  cells to accepted bundled assets; widgets reuse existing `lang` and
  `font-family` properties, and shared WM windows preserve explicit language
  while `und` retains the old monospace default. Draw IR SDN now round-trips
  shaped glyph IDs, positions, and clusters and drops malformed parallel arrays
  without indexing them. Focused source assertions cover `zh/mono` fallback and
  Hindi/Arabic/Urdu sans selection. Numbered-artifact, direct-env working/staged,
  rendering-source-coupling, and `doc/06_spec` layout guards pass; full
  `git diff --check` passes after mechanical CRLF normalization in four Vulkan
  Rust files. The focused Draw IR SDN spec could not execute because Stage53
  rejects pre-existing named-argument syntax before the changed code. No
  generated manual, native pixel/perf evidence, verify PASS, or sync claim is
  made. STATUS: FAIL.

  Independent host checks additionally match all 16 bundled font binaries to
  their registry SHA-256 values, and `cargo test -p spl_fonts --lib` passes all
  9 native font-provider tests. These prove immutable bytes/provider behavior,
  not the blocked Pure Simple or device evidence gates.

- Shaped baseline/bearing repair (2026-07-13): the shared renderer now applies
  one checked PositiveYDown destination rule to both semantic shaped payloads
  and the older neutral glyph-run adapter. OpenType y offsets are negated when
  the run is built; rasterizers retain native horizontal bearing and bitmap
  bottom offset; the executor reconstructs top-left as
  `x = pen_x + bearing_x`,
  `y = ascent + pen_y - bearing_y - bitmap_height`. The legacy stb runtime now
  exposes bitmap x/y offsets and ascent, and the native C font-bytes test passes.
  A focused Rust provider test independently proves the same destination rule,
  and the rendering-source-coupling and `git diff --check` guards pass after the
  repair. Source-level Arabic assertions cover the exact resulting quad, but the
  blocked self-host still prevents the canonical Simple pixel oracle and docgen;
  shader artifact provenance, device readback/RSS, verify PASS, and sync remain
  unavailable. STATUS: FAIL.

- Bootstrap root-fix continuation (2026-07-13): the first unsafe Stage55
  fallback had one concrete type-inference cause: each ownership variant of
  `ComponentStats.get_metric` returned either an `f64` metric or `nil` without
  declaring `f64?`, so LLVM received an inferred `i64` function signature and
  rejected the `f64` return. All three mechanically mirrored definitions now
  declare `-> f64?`; `git diff --check` passes. The mandatory three-cycle cap
  forbids another bootstrap retry in this session, so this is a source repair,
  not accepted self-host or verification evidence. STATUS: FAIL.

- Native font-codegen provenance continuation (2026-07-13): a proposed shortcut
  that concatenated optimization and font sources into one artifact was rejected
  because the selected contract requires a distinct `_font_atlas` companion (and
  WGSL bindings conflict). The existing toolchain checker now runs both Simple
  emitters once, splits their marked outputs, separately compiles CUDA PTX, HIP
  HSACO, OpenCL SPIR-V, and Metal metallib companions, and fails aggregate target
  status unless both artifact symbol sets validate. Its report records separate
  paths, byte counts, statuses, reasons, and commands; shell syntax and focused
  diff integrity pass. The same checker now emits canonical Vulkan GLSL and
  compiles/validates a distinct `.spv` companion through glslang or glslc.
  SPipe additionally requires proof that a promoted runtime
  loaded that same verified companion. The capped emitter/toolchains were not
  executed, and current CUDA/Vulkan runtime blobs remain independently authored/
  generated, so runtime provenance is still open. STATUS: FAIL.

  A new independent host cmap audit also found every distinct codepoint from
  the exact ten ranked witnesses in the three promoted sans assets (`10/10`,
  no missing codepoints). That proves bundled cmap bytes only, not shaping or
  canonical Simple execution.

- Shaped CPU oracle source continuation (2026-07-13): the exact accepted Arabic
  test now requires a nonzero native bearing, checks the reconstructed quad
  origin, and compares every composed atlas alpha byte with an independently
  rasterized glyph snapshot. This strengthens the source oracle without another
  fixture, but it remains unexecuted under the capped self-host and is not device
  parity evidence. STATUS: FAIL.

- CUDA generated-companion runtime seam (2026-07-13): `CudaSession` now owns an
  optional bounded font-only PTX module separate from the compatibility/2D
  module, pins its exact SHA-256 identity, rejects replacement, launches font
  quads from it when installed, and unloads it with the session. Engine2D exposes
  `install_cuda_font_ptx`; the existing 8-byte argument slots are also valid for
  the generated kernel's bounded low-32-bit scalar ABI. The shared CUDA loader
  also now rejects negative runtime error codes instead of caching them as module
  handles. A focused source test
  covers validation and immutable identity without CUDA hardware. The later
  generated-only hardening removed the default handwritten entry; the
  unexecuted install/device-readback path is not promotion evidence. STATUS: FAIL.

- Stage-54/55 bounded bootstrap continuation (2026-07-13): the three explicit
  `ComponentStats.get_metric -> f64?` repairs cleared the verifier fallback;
  Stage54 compiled 1,065 cached/current modules and reached final linking. Its
  older Stage53 linker still omitted the supplemental core C runtime, so
  `rt_mkdir_p`, `rt_font_*`, and other owned runtime symbols remained
  unresolved. The current Rust seed/native archive then rebuilt successfully
  in 4m58s, incorporating the already-reviewed supplemental-runtime linker
  path. A source-exact Stage55 bootstrap attempt exposed two package-export
  collisions before compilation: `intersection_type_get_members` was declared
  again as an extern in `type_checker.spl`, and the AOP parser privately
  reimplemented `is_alpha`. Both now reuse their canonical owners in
  `types.spl` and `lexer_chars.spl`; no fourth rebuild is permitted by the
  three-cycle cap. The portable-compute report also now names its cross-host
  aggregate `all_portable_compute_toolchains_verified`, avoiding a false claim
  that every OS toolchain is required for one-backend promotion. No accepted
  self-host, verify PASS, commit, rebase, or push exists. STATUS: FAIL.

- Stage55 package-owner recovery and configuration contract (2026-07-13):
  three strict source-exact preflights exposed `mono_cache_register`,
  `named_type_field_type_tags`, and `parse_addition` as ambiguous package
  exports. The first two families now use distinct/canonical owners; the third
  was traced to a legitimate parser facade re-exporting the same sibling
  implementation. Bootstrap discovery now prefers a sibling that explicitly
  defines a requested symbol over a bare-export facade that only imports it,
  while retaining the facade as an implicit fallback. Its focused Rust package
  discovery regression passes (1 passed, 0 failed). The bootstrap seed must be
  rebuilt once before the next Stage55 attempt; the three-cycle cap forbids that
  rerun here.

  Higher-model audits also identified the missing AC-8 trace and exact REQ-009
  gaps. REQ-015 now specifies one text-layout-owned runtime configuration and
  observable Suggested/Preferred/Required target policies; detail design, the
  shared font guide, Codex SPipe dev/system-test skills, and the Claude SPipe
  mirror carry the same fail-before-mutation evidence rule. This is a contract
  correction, not runtime implementation or evidence. Emoji remains a pinned
  candidate until exact-face shape-to-`FontRenderBatch` executes; legacy
  SimpleOS still requires a frame-level Draw IR migration rather than another
  private font adapter. No accepted self-host, verify PASS, commit, rebase, or
  push exists. STATUS: FAIL.

- Exact-identity static hardening (2026-07-15): lower-model shaping and GPU
  audits found two shared-boundary gaps, and the primary high-capability review
  accepted the minimal fixes. `shaper_with_ot_face` now rejects an OpenType
  blob whose SHA-256 does not match the live face identity. Vulkan font
  installation and promotion now require the exact pinned SPIR-V hash rather
  than accepting any magic-valid module, and CUDA reuses the common versioned
  entry constant. Focused source tests cover cross-bound faces, blob drift,
  unpinned SPIR-V, and exact stage evidence. No Simple runtime, docgen, native
  GPU, QEMU, or performance command ran after the three-cycle cap; the three
  serif cells, seven manual regenerations, and retained device evidence remain
  pending. STATUS: FAIL.

- Generated-only CUDA font dispatch (2026-07-15): parallel static audits and
  primary review removed the handwritten font PTX from the default CUDA 2D
  module. Font launch now requires the distinct installed generated-PTX module
  and fails before atlas mutation when it is absent, preserving CPU replay from
  quad zero for Suggested/Preferred policy and fail-closed Required behavior.
  Unit/manual SPipe, architecture, design, guide, and skill contracts now match.
  No Simple runtime, docgen, native GPU, QEMU, or performance command ran after
  the three-cycle cap; retained generated-device evidence remains pending.
  STATUS: FAIL.

- SimpleOS font-evidence schema repair (2026-07-15): the canonical desktop
  success marker now binds the selected Noto Sans Mono hash, pure `glyf`
  rasterizer, Draw IR route, font size, text, crop, and crop hash exactly as the
  host evidence wrapper requires. Source-contract tests and manuals match.
  The expected crop hash and retained QEMU run are still pending; no runtime or
  QEMU command ran after the three-cycle cap. STATUS: FAIL.

- CUDA production deployment audit (2026-07-15): all Engine2D constructors
  converge on `create_requested_backend`, but no tracked trusted font PTX or
  immutable deployment manifest exists. The checker output under ignored
  `build/` is mutable evidence, not a production trust anchor, so automatic
  loading was not added. Package the generated PTX with a pinned manifest/hash,
  then reuse the existing installer in the canonical factory. STATUS: FAIL.

- Legacy direct-entry scope audit (2026-07-15): the x86 compatibility demo has
  192 static private text sites but only nine reachable calls, all through one
  private vector helper. Selected REQ-011 already routes canonical producers
  through `DrawIrComposition` and Engine2D and explicitly excludes direct
  `arch/*/wm_entry.spl` from production evidence, so no duplicate migration was
  added. Retained canonical QEMU pixels remain pending. STATUS: FAIL.

- CUDA trust-boundary documentation review (2026-07-15): three parallel
  read-only audits and primary review confirmed that all canonical Engine2D
  construction converges on `create_requested_backend`, but the generated PTX
  and adjacent evidence are missing ignored build outputs whose co-produced
  hash is not an independent trust anchor. The tracked embedded Vulkan artifact
  is the reusable production pattern; no generic trusted artifact loader exists.
  The current package verifier skips checksum comparison and its builder emits
  `checksum_placeholder`, so no automatic CUDA install was added. Architecture,
  design, guide, system manual, test plan, tracking bug, Codex SPipe skills, and
  the Claude mirror now require packaged or tracked Simple-generated PTX bound
  to an immutable hash/program version, forbid production loading from ignored
  build output, and keep conditional checker evidence distinct from deployment.
  The stale CUDA backend manual now lists all 18 source scenarios. No Simple
  runtime, docgen, native GPU, QEMU, or performance command ran after the
  three-cycle cap; production CUDA packaging and device evidence remain pending.
  STATUS: FAIL.

- Catalog and SimpleOS static coverage repair (2026-07-15): parallel catalog,
  GPU-owner, and SPipe/manual audits revalidated all 16 licensed assets, the
  exact top-ten language order, all ten categories, the honest 67/4/26/3 matrix,
  one shared 2D/3D batch owner, and all six source-emission contracts. The
  manifest scenario now asserts every candidate's pinned script metadata, and
  the SimpleOS integration scenario now covers the Simple Browser's long-path
  then short-alias lookup, canonical registration, and exact 16-face fail-closed
  gate. The system-test plan now lists all seven feature specs in execution
  order. The provisional manual vocabulary near the start of this state is
  superseded; the five frozen phrases remain exactly:
  `Load the pinned multilingual font manifest`,
  `Accept exact-face-bound simple-script shaping`,
  `Prepare one shared font batch for 2D and 3D`,
  `Emit the selected font composite program and plan compilation`, and
  `Prove native submission and device readback`.
  No Simple runtime, docgen, native GPU, QEMU, or performance command ran after
  the three-cycle cap; executable evidence remains pending. STATUS: FAIL.

- Verifier mirror synchronization (2026-07-15): Codex, generic-agent, Claude
  SPipe spec/verify, and Gemini verification surfaces now reference their
  canonical CUDA font artifact-trust rule before accepting production PASS.
  The rule remains single-owned by the existing Codex system-test and Claude
  SPipe skills; no duplicate loader or policy implementation was added. No
  runtime or device command ran after the three-cycle cap. STATUS: FAIL.

- Fresh-session CUDA resume contract (2026-07-15): the tracking bug and shared
  font guide now give one bounded NVIDIA-host checker command using the current
  pure-Simple `bin/simple` and `CUDA_ARCH=compute_75`. Acceptance requires the
  font-specific compiled status, exact entry, and current Simple/emitter/source/
  artifact provenance; the checker-adjacent hash remains evidence and cannot
  replace an independent package/tracked trust anchor. The command was not run
  after the three-cycle cap. STATUS: FAIL.

- Pure-runner and process-doc refresh (2026-07-16): the final bounded full-CLI
  build passed Stages 2/3, then failed after more than one hour and 5.6 GiB RSS
  because the pure Stage-4 parser rejects tuple destructuring in
  `for name, lit_def in literals_config.custom`. No candidate reached seedless
  admission, so seven native specs, seven canonical manual regenerations,
  performance/native-GPU records, and the SimpleOS crop hash remain pending.
  The focused-runner argv/no-fallback/process-facade/exit/stderr/cleanup contract
  is synchronized across Codex, generic-agent, and Claude SPipe instructions.
  `.gemini/commands/` contains no command files for this lane, so its mirror is
  explicitly N/A rather than invented. STATUS: FAIL.

- Current-main truth review (2026-07-17): parallel manifest, documentation,
  and implementation audits rechecked clean `origin/main` at `92248f477db`.
  The exact top-ten language order, ten categories, sixteen tracked licensed
  assets, honest 67/4/26/3 matrix, shared `FontRenderer`/`FontRenderBatch`,
  Draw-IR Web/GUI/WM routes, separate Engine3D consumers, portable emitters,
  and source-tracked CUDA PTX trust gate are present. Completion is still
  blocked: no admitted current pure-Simple runner or canonical docgen output;
  no retained native device, performance, or QEMU font-pixel evidence;
  registered-only SimpleOS shaping cannot yet accept Arabic/Devanagari runs;
  and the baremetal invalid-metrics route draws placeholder bars. Review also
  found raw `rt_mutex_*` ownership in `font_renderer.spl` and a hosted-racy
  scalar atlas generation counter. It also flagged a mutable module-global
  Engine2D pool at the audited baseline; intervening commit `4d3f37e3e9e`
  removed that pool before this refresh landed. The remaining findings are
  source blockers, not evidence passes. No runtime command ran and no PASS is
  claimed. STATUS: FAIL.

- Facade-lock and WM fallback repair (2026-07-17): the generic runtime mutex now
  holds exclusion through explicit unlock and rejects foreign/double unlock;
  the shared Pure Simple renderer uses hosted-eager, freestanding-lazy typed
  facade locks for both caches and the atlas generation counter. The WM
  invalid-metrics branch therefore emits the canonical legacy bitmap text
  command again instead of a two-pixel rectangle placeholder. Focused runtime
  mutex tests passed 3/3, the standalone framebuffer runtime target passed 3/3,
  static renderer/WM contracts and rendering/direct-runtime guards pass, and
  independent high review accepted both source lanes. No admitted current
  pure-Simple runner or retained QEMU pixel capture exists, so no native font
  or SimpleOS pixel PASS is claimed. STATUS: FAIL.

- Registered-only shaping repair (2026-07-17): the exact pinned Arabic/Urdu and
  Hindi witnesses now bind validated registered OpenType blobs directly to the
  existing pure-Simple shaper with handle/generation zero, then materialize the
  handle-free Draw IR payload through the existing selected-byte
  `FontRenderer`/`FontRenderBatch`. The route does not call SimpleOS's stubbed
  host font ABI. A focused unit reproduction, SimpleOS source-contract guard,
  and final irreversible SPipe scenario cover shaping plus nonempty batch
  preparation. Static direct-runtime and rendering-coupling guards pass; no
  admitted current pure-Simple runner, docgen result, or retained QEMU pixels
  exist, so executable and guest evidence remain pending. STATUS: FAIL.
