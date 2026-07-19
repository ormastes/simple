# Shared Multilingual GPU Fonts

This guide separates the selected contract from what the current source proves.
The feature consolidates font selection and material preparation under the
existing `FontRenderer`; it does not introduce a second renderer.
Use `$sp_dev` as the process owner for bundled-font, shaping, glyph-material,
and GPU-text development lanes.

## Selected coverage

The reproducible CLDR 48.2 literate-functional ranking is:

`en`, `zh`, `es`, `hi`, `ar`, `fr`, `pt`, `ru`, `ur`, `id`

`bn` is retained as the eleventh-place boundary and useful extra candidate
coverage. The selected scripts are Latin, Simplified Han, Devanagari, Arabic,
and Cyrillic.

`common.encoding.font_cldr_rank` now provides the deterministic fixed-decimal
scanner, alias policy, per-script aggregation, and lexical tie break used by a
focused synthetic fixture. The exact CLDR 48.2
`common/supplemental/{supplementalData,supplementalMetadata,likelySubtags}.xml`
bytes, annotated-tag witness, source manifest, license, and derived top-eleven
ledger now live under `assets/fonts/cldr/release-48-2/`; their SHA-256 values
match the pinned upstream object. The real-input SPipe scenario regenerates the
ledger twice, independently recomputes all 1,589 contributions, and compares
every language total and script subtotal. This source is ready for that gate,
but no fresh Simple execution ran in this capped session, and the targeted
start-tag scanner remains non-validating XML.
The arithmetic fixture is
`test/01_unit/lib/common/encoding/font_cldr_rank_spec.spl`.

The ten product categories are sans, serif, mono, display, rounded,
handwriting, slab, blackletter, pixel, and emoji. This is a product taxonomy,
not a popularity ranking. Each language/category cell must say `native`,
`fallback`, `not-designed-for-script`, or `unavailable`; decorative Latin faces
must not be presented as native coverage for every language.
Here `native` means an accepted direct category face, not native GPU execution;
`fallback` means an explicit edge to another accepted face. Codepoint coverage
alone proves neither status.
Use `selected_font_coverage_cell(language, category)` for exact policy lookup;
use `selected_font_asset_for_language_category(language, category)` when a
renderer needs the corresponding bundled face. It returns only promoted
`native`/`fallback` candidates and returns `nil` for unavailable, not-designed,
or unknown cells.

`validate_selected_font_asset(path, blob)` hashes the supplied bytes and is the
required boundary for byte APIs. File callers use
`load_selected_font_file(path)` so the validator owns the read and returns the
same verified bytes. Transformed, cached, or caller-supplied bytes must use the
strict byte API. Both paths hash the exact returned/supplied bytes and apply the
same length, sfnt/default-axis, table, and embedded name checks.
unknown axes return `nil`. Do not load `witness_family` while the cell is
`unavailable` or `not-designed-for-script`.

Both native roots initialize exact selected bundled-font paths from their same
owned verified bytes. The shared validator hashes bounded `[u8]` storage
directly after checking the pinned byte length and before parsing font tables.
`spl_fonts` also passes the pinned digest to `rt_fonts_init_verified_bytes` for
a native defense-in-depth recheck; `font_sffi` calls `rt_font_load_bytes`.
Equivalent aliases and other unmanaged fonts retain legacy path loading and are
outside the race-free claim. Neither path promotes a coverage-matrix cell.

## Pinned candidate assets

`selected_font_asset_candidates()` records 16 unchanged files from Google Fonts
commit `ec0464b978de222073645d6d3366f3fdf03376d8`, including script-specific Noto
Sans/Serif faces and these category witnesses: Noto Sans Mono, Bungee, Nunito,
Caveat, Roboto Slab, UnifrakturCook, Pixelify Sans, and monochrome Noto Emoji.
The catalog records paths, SHA-256, byte size, tables, scripts, license,
copyright, RFN state, upstream revision, embedded style/full/PostScript names,
embedded version, default variation axes, fallback role, and a hashed reference
to the canonical multilingual witness corpus.

The manifest scenario replays the pinned family, subfamily, full, PostScript,
and version strings from every real binary's sfnt `name` table. Runtime
loading enforces the same embedded names. This exact identity check does not
promote language/category coverage.

The unchanged binaries and adjacent metadata/licenses are bundled under
`assets/fonts/google-fonts/` (16 files, 51,764,704 font bytes). Twelve are
accepted in source policy—nine identity-profile families, the sans Devanagari
and Arabic witness faces, and exact-corpus Noto Emoji. Serif Devanagari/Arabic
and two rank-eleven Bengali faces remain candidates.
`selected_font_bundle_asset_pins()` is the single immutable distribution list:
49 paths derived from the 16 candidate binary/metadata/license/notice fields,
plus `CORPUS.sdn` and seven pinned CLDR resources. The distribution-size gate
requires that exact 57-path set, then counts root `LICENSE` and
`THIRD_PARTY_NOTICES.md`: 59 files and 53,433,272 bytes against the 80 MiB
ceiling.
Before its first font copy, the release installer rejects a wrong pin count,
missing or extra source paths, missing bytes, or a source hash mismatch. It
copies only pinned paths and verifies each destination against the same hash;
`LICENSE` and `THIRD_PARTY_NOTICES.md` remain separate root resources below
`share/simple`. Its wrapper exports that share directory as `SIMPLE_ASSET_ROOT`;
the registry byte-load boundary resolves the same canonical paths there.
Portable bootstrap/full archives also bundle the
tree and launch `simple-runtime` through an asset-root wrapper. Unix installer
packages use `/usr/local/share/simple`; Windows portable/NSIS packages use the
installed package root. A configured
installed root takes precedence; without one, repository-relative paths remain
unchanged. The resolver accepts any nonempty share or portable package root,
normalizes trailing separators and Windows backslashes, and appends only the
registry-owned relative asset path; unmanaged paths are never redirected.
Installed paths do not create a second catalog or change pinned identities.
SimpleOS images use the OS-owned `simpleos_font_bundle_entries()` projection:
all 50 Google Fonts files, the CLDR license, root `LICENSE`, and
`THIRD_PARTY_NOTICES.md` (53 files / 51,932,523 bytes). The six CLDR
XML/tag/source/ranking inputs stay host-build evidence because the guest uses
the compiled ranking, not those inputs. Existing TTF long paths and 8.3 aliases
remain unchanged; metadata, licenses, corpus, and notices use unique 8.3
siblings below `/SYS/FONTS`. The legacy C writer checks the 16 TTF hashes plus
the exact 35-entry pinned companion manifest before mutation and uses 91 of its
128 font-directory entries.
The two serif script candidates have bounded default-instance source profiles
and independent glyph/advance/offset probes. They remain unavailable to normal
selection because the retained full pure-Simple CLI has not executed those
probes; do not substitute the Rust seed or infer acceptance from source review.
The canonical font provider now projects all 16 manifest paths and accepts an
exact, trimmed, case-insensitive family name as a singleton candidate. Encoded
`@font-face` sources still take priority; generic CSS family heuristics remain
unchanged. Runtime addressability does not promote any sparse-matrix cell.
Do not call a face supported until shaping/codepoint tests and the sparse matrix
accept it. The selected policy permits only unchanged default variable-font
instances and requires non-default axes plus color/SVG/strike/CFF tables to
fail closed. Both native loader owners now call the Pure Simple structural
preflight before native state changes; it validates directory bounds/overlap,
required/excluded tables (including legacy `bdat`/`bloc` bitmap strikes), and
`fvar` defaults. `validate_glyf_font_instance` accepts only `static` or the
exact declared default-axis tuple; non-default and unknown requests fail closed
before native loading/cache mutation. Focused source coverage repeats a Pure
Simple raster of pinned Pixelify Sans at `wght=400`, pins its `15x21`
dimensions, `19` advance, and raster SHA-256, and pins the built-in 8×16
monochrome `A` glyph. The deployed compiler prevents executing these refreshed
checks, so REQ-008 remains unverified rather than promoted; this source oracle
is not a new runtime PASS claim.

A complete raw audit found 7,594 compound glyphs (16,194 components) in 14
candidate faces; the exact witness corpus reaches 76 roots/124 direct
components. The bounded glyph-ID Pure Simple parser now reconstructs and
rasterizes those roots with bounded dimensions and exact integer metrics.
The typed native wrapper retains the already validated selected bytes and uses
the neutral common cmap/glyf rasterizer only for a current selected face after
the native call returns the zero no-glyph handle. Negative native errors,
unmanaged/CFF faces, absent mappings, stale wrappers, and malformed nonzero
handles fail closed. Native success remains unchanged, no per-glyph file I/O
occurs, and close releases the retained bytes. No coverage cell is promoted.

The manifest scenario prepares exact `CORPUS.sdn` codepoint and raster
witnesses for all 16 candidates, including Bengali rank 11 and Noto Emoji
`U+1F600`. The current source policy retains 54 no-feature identity native
cells, accepts the sans faces for the exact Hindi and Arabic/Urdu witnesses,
and accepts exact monochrome Noto Emoji `U+1F600` corpus tuples for all ten
selected language tags. The matrix totals are 67 `native`, 4 explicit
script-sans mono `fallback`, 26 `not-designed-for-script`, and 3 `unavailable`;
the last promoted-baseline shaping/material scenario exited 0. The refreshed
scenario with pending serif probes has no current runner PASS. The pinned
release artifact SHA `04a38e21…` exits 139 before assertions; the latest
retained candidate reaches a distinct recursion guard. Both are tracked in
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`.
An accepted identity cell means
the exact pinned face stayed live, parsed cmap and runtime glyph IDs agreed for
the exact language witness, bounded hmtx advances matched, shaping completed,
and canonical material was produced. Chinese, Hindi, Arabic, and Urdu `mono`
use explicit fallbacks to their accepted script sans faces while retaining the
Mono request. Exact Hindi `हिन्दी` and Arabic/Urdu witnesses cover the accepted
sans faces; serif remains candidate-only. Other complex sequences, general emoji sequences/color,
GPU execution, and the refreshed source-policy run remain incomplete.
The pending serif probes pin Noto Serif Devanagari glyphs and Noto Naskh
Arabic/Urdu GSUB/GPOS results, reject wrong-language pairs, marks, profile
drift, and non-default axes, and require nonzero canonical material per glyph.
They are readiness evidence only until a working deployed pure-Simple CLI runs them.

## Current shared material

The canonical implementation is
`std.nogc_sync_mut.text_layout.font_renderer.FontRenderer`, re-exported through
the other ownership variants. It now exposes:

```simple
val batch = renderer.prepare_text(content, color, font_size)
```

`FontRenderer` owns one bounded 1024×1024 shelf-packed white-alpha atlas.
`FontRenderBatch` carries stable per-glyph destination/atlas quads, codepoint and
byte-offset identity, color, exact font identity and face generation snapshots,
atlas generation, the shared pixels, and only the new dirty rectangles.
Repeated warm glyphs keep coordinates/generation and
produce no dirty upload. Face changes or capacity overflow reset and repack the
atlas. Engine2D uses its established `load_font`/`draw_text` surface, and
Engine3D consumes the same batch through its CPU fallback or optional Vulkan
HUD/world adapter. Its `draw_glyph_run_hud` and `draw_glyph_run_world`
entrypoints reuse the same neutral material, renderer, atlas, and
stale-generation rejection. CPU world placement is a projected billboard; the
Vulkan world pipeline tests/writes depth and discards zero-coverage fragments,
but remains unpromoted until the retained device oracle passes.

The native rasterizer reads generation on both sides of its identity snapshot.
A stale snapshot is neutral `(0, "")`, and a mid-preparation identity change
discards that transient batch. This does not make process-global replacement
atomic and does not claim a global lock.

CPU code remains responsible for face selection, rasterization, fallback, and
cache identity. Complete Pure Simple complex-script shaping/BiDi is still a
tracked prerequisite; the built-in bitmap path remains the zero-config fallback.
Fontdue remains the basic layout/raster owner, while FreeType and stb provide
rasterization/metrics; none is shaping evidence. System HarfBuzz is not a
declared uniformly available dependency, and Rustybuzz is not added under
the selected Pure Simple contract.
The OpenType parser now supports validated Unicode cmap formats 4 and 12,
including bundled Noto Emoji `U+1F600`. Mixed-face fallback is accepted only
for the exact Chinese-mono-to-Noto-Sans-SC row; broader per-script fallback
still requires complete GSUB/GPOS and corpus evidence.
Hosted shaping binds OpenType data by exact fallback face handle/generation; an
unbound or stale attached face never borrows another face's blob, and the blob
SHA-256 must match the live face identity. Registered-only SimpleOS instead
accepts only the exact validated registered blob with handle/generation `0`.

The opt-in shaped path now keeps each `ShapedGlyph`'s absolute source index,
cluster, current advance, and explicit zero offset through Arabic reversal,
provisional Devanagari reorder, and Thai mark clustering. `ShapedRun` adds
caller language identity (empty becomes `und`) while retaining script and
script-direction identity. Latin-1 letters no longer split Spanish, French, or
Portuguese witness runs, and mixed-script runs advance instead of overlapping.

Bind each OpenType blob to its runtime face with additive
`shaper_with_ot_face` calls; rebinding a handle replaces its prior snapshot.
Latin, Cyrillic, Han, and a whole-run single-codepoint emoji may complete only
when the selected live face and blob/runtime cmap glyph IDs agree, hmtx advance
matches, and canonical material is valid. Exact monochrome Noto Emoji
`U+1F600` has passed that focused self-hosted gate for every selected language
tag and is matrix acceptance only for that corpus tuple. The bounded
Arabic/Urdu path validates selected Script/LangSys
metadata and executes witness-specific pinned lookup indices/forms for the two
promoted literals; it does not claim general substitution/positioning completeness. The exact Hindi `हिन्दी`
witness selects bounded `dev2` Script/LangSys records and ordered default GSUB/
GPOS feature tags, with a HarfBuzz glyph/advance oracle; discretionary or
inactive lookups and other Indic sequences fail closed. Marks, Bengali, Thai,
Hebrew, variation-selector/modifier/ZWJ/color emoji, and multi-codepoint emoji
also fail closed. Convert
substitution-complete
accepted runs with
`shaped_run_to_font_glyph_run`; incomplete runs remain non-renderable even when
their pre-GSUB glyph indices match. Engine2D consumes only that neutral text-layout
value through `draw_glyph_run`, preserving the batch-only layer boundary. It
carries a revocable generation token rather than a native face pointer. Hosted
material rejects mismatched or freed face handle/generation pairs and keys
cache/atlas entries by face + lifetime generation + glyph index + size;
registered-only material uses the handle-free payload with the existing
selected-byte rasterizer identity/generation. This is a bounded
renderer seam, not complete mixed-face GSUB/GPOS or automatic `draw_text`
shaping. The identity subset is the 54-native/1-fallback evidence above; exact
Hindi and the exact pinned Arabic/Urdu lookup-vector cases are separately
bounded to their proven witnesses.

REQ-009 source cases are complete: selected checksum/default-axis identity now fences the
glyph cache, atlas, and resolved-metrics cache; stats expose that identity, and
generation-bound wrappers over the process-global face are revocable so stale
operations fail closed. A batch derives an atlas-owner identity from its live
font identity, face generation, numeric program version, and dimensions, then
adds atlas generation for the backend cache identity. CUDA, OpenCL, Metal, ROCm, and
Vulkan reuse an upload only when both backend-local owner and generation match.
Focused unit specs cover these keys and bounded cache counters; the shared
surface SSpec covers warm generation and dirty regions. Conditional real-dylib
A-to-B evidence remains unexecuted under the session cap. A shared mutex
protects the process metrics ring; it retains at most 128 requests and bypasses caching when family length
exceeds 1,024 or content length exceeds 4,096. Canonical raster scale is
`font_size` and already participates in the glyph, atlas-entry, and metrics
keys; translation is late-bound and does not change atlas material. Other CTM
components remain unsupported. Backend-device and runtime program-artifact
identity do not share one cache concern: atlas buffers are destroyed before a
device is destroyed, while an active CUDA, OpenCL, or Vulkan backend rejects
session replacement and Metal releases font state before device recreation.
ROCm keeps its atlas inside one backend lifetime and releases it with the HIP
module at shutdown.
Configuration identity now invalidates and keys canonical glyph material and
is length-delimited into shaped-run keys and every configured batch/atlas owner.
Shared multi-face batches carry the renderer's explicit atlas-owner generation;
a caller-supplied `font-faces-v1` string cannot claim shared ownership.
`FontRenderBatch.material_supported()` rejects unknown atlas-composite program
versions and noncanonical transforms before Engine2D or Engine3D mutation.
Remaining REQ-009 gaps are runtime compiled-artifact identity, resolved-run and
atlas telemetry, native execution evidence,
and concurrent multi-face ownership. None promotes the coverage matrix.

### Runtime configuration contract

The public surface is `FontRenderConfig` beside `FontRenderBatch`,
with family/category/language/script, size, weight/style, hinting,
antialiasing, shared-atlas policy, execution target, and
`Suggested`/`Preferred`/`Required` policy. The config object, atlas/execution
policy, caches, and native resources do not cross WebIR or Draw IR. Existing
semantic family/language/size/style fields and handle-free shaped payloads do;
Engine2D combines them with runtime-owned config. Existing size-only calls
remain default-config adapters.

The default is normal style/weight, no hinting, grayscale coverage, the shared
1024 alpha atlas, target `auto`, and `Suggested`. `Suggested` tries the named
target first, then the remaining canonical GPU order, then CPU; `Preferred`
tries its named target then CPU; `Required` tries only its named target and
fails without another GPU or CPU attempt. `Suggested(auto)` uses Engine2D's
executable `cuda, metal, opencl, vulkan, rocm, cpu` order or Engine3D's
`vulkan, cpu` order. Preferred/Required require a concrete supported target;
concrete `cpu` is valid. Unknown targets and unsupported
rendering modes or nonuniform/rotated/skewed/subpixel transforms must reject
before changing cache generations or backend state. The canonical renderer and
Engine2D/Engine3D owners now implement those configured entrypoints and retain
an observable attempt/selected-target trace. A non-default
family/category/language/script tuple resolves through the pinned sparse matrix,
requires the exact resolved family (or `auto`), validates the CLDR script, and
loads the unchanged bundled face; unavailable tuples reject before cache
mutation. Engine3D fixes one font target per frame and promotes Vulkan from
`pending` to selected only after end-frame device readback evidence. Focused
unit and shared-surface specs cover source behavior; REQ-015 remains open until
the deployed pure-Simple runtime executes those specs successfully. The exact
Stage 4 provider work resolved the earlier 208-symbol link failure and produced
one full CLI before the scalar test-argv bridge landed. That older binary is not
current acceptance evidence. Later bounded current-source runs stopped at
different parser, LLVM construction, and resource-growth failures; none
produced an admitted candidate. This is a compiler/runtime deployment defect,
not font-source failure, and neither a seed, minimal-stage binary, nor the
pre-bridge full CLI is native acceptance evidence.
A fresh full CLI has not yet been admitted. The exact binary digest, command,
GDB failure site, retained-candidate recursion result, and bounded
bootstrap failure are recorded in the tracked deployment bug linked above;
none is font acceptance evidence.

Current evidence limitations must remain visible during that recovery.
Registered-byte-only source paths now accept the exact pinned Arabic/Urdu and
Hindi witnesses through validated handle-zero OpenType binding and materialize
the handle-free payload with the existing selected-byte renderer. A focused
unit reproduction, SimpleOS source guard, and SPipe regression protect that
route. The freestanding WM invalid-metrics branch retains readable canonical
legacy bitmap text after the shared renderer locks and atlas generation moved
behind the existing mutex facade. Neither source route is retained QEMU
pixel-oracle evidence.

Canonical `FontRenderer` fallback glyphs are rasterized on CPU. Environment-
published accelerator pixels are compatibility-only diagnostics and cannot
enter `FontRenderBatch` or its cache; GPU backends only compose the prepared
alpha atlas.

## GPU code emission is not execution

Simple compiler code provides
`emit_portable_font_atlas_composite_kernel(target)`. It emits the versioned
`simple_font_atlas_composite_v1_u32` entry for CUDA, HIP, OpenCL, Metal, and
WGSL. `emit_vulkan_font_atlas_composite_source()` separately returns the
canonical Vulkan GLSL 450 source for GLSL-to-SPIR-V compilation; Vulkan is not
a `PortableComputeTarget`, and source emission is not compilation or execution.

```simple
use compiler.backend.gpu_portable_compute.{PortableComputeTarget, emit_portable_font_atlas_composite_kernel}

val artifact = emit_portable_font_atlas_composite_kernel(PortableComputeTarget.Cuda)
print artifact.source
```

Choose another portable target to emit its source; inspect the matching compile
plan before invoking a toolchain. Printing source proves emission only.
For a stable command surface, run
`bin/simple run src/app/portable_compute_emit/main.spl cuda`; the accepted
targets are `cuda`, `hip`, `opencl`, `metal`, `webgpu`, and `vulkan`. The app
calls these same compiler emitters and prints delimited source plus source and
version SHA-256 markers. It does not compile, install, or execute an artifact.
The Vulkan shader's 15-input ABI is two storage-buffer bindings plus the exact
contiguous 13-field parameter block, and its entry is `main`.
`vulkan_font_atlas_compile_plan` records canonical source and external
GLSL-to-SPIR-V metadata; its evidence contract fails closed on missing bytes,
bad magic, or missing `main`. A valid synthetic contract is not compilation or
execution, and no compiled artifact exists absent real external capture.
Native-target signatures include explicit atlas/destination element counts,
reject invalid atlas subrects before origin/index addition, and guard computed
indices. WGSL rejects nonpositive dimensions, negative atlas
origins, overflowing products, invalid subrects, and destination-add overflow
before unsigned casts, then uses `arrayLength` for the final buffer bound.
Portable backend planning emits a separate optimization artifact and font
companion artifact for each selected target. The font path uses the
`_font_atlas` suffix and requires the versioned composite entry; it is not
concatenated with the optimization module (especially for WGSL, whose bindings
conflict). `check-portable-compute-toolchains.shs` invokes the tracked
`portable_compute_emit` app, splits its two marked outputs, and compiles
distinct native companions; a target is verified
only when both artifacts export their required symbols. Its retained
`evidence.env` records the configured Simple invocation path/SHA-256 separately
from its resolved native ELF or Mach-O runtime path/SHA-256, canonical emitter source/version
hashes, generated-source SHA-256, compiler executable/version,
and compiled artifact SHA-256/bytes/required symbols. The checker emits source
bytes only through the raw emitter protocol and rejects them before compilation
unless their SHA-256 equals the emitter-declared source hash for both the
optimization and font companions. It also emits canonical Vulkan GLSL and
compiles a distinct Vulkan 1.1 `.spv`, preferring the
pinned artifact's `glslc` recipe with glslang as a fallback, but accepts it only
when the canonical source and fresh artifact
match the pinned
`c94b13736bdf7022835c008c09d714507da4cd0b6ef4607a5eadc9a23549cd2c`
and `e25d25b8157fc2554822637603471a442f678eb58e20da167bfb023d7577880a`
identities exactly. A mismatch
fails closed; the checker does not install its fresh artifact. Missing or
malformed source hashes stop before compilation. A well-formed stale source is
compiled and its `.comp`/`.spv` candidate is retained for review. It may report
candidate compilation and artifact validation, but pin verification remains
false; only matching source and artifact pins may report
`compiled_artifact_verified`. Production keeps
the independently pinned embedded SPIR-V, but `VulkanSession` currently rejects
its stale semantics before resource creation.
CUDA compile plans use
`nvcc --ptx -o <output> <source>`; the kernel
symbol is verified from the artifact rather than passed through a nonexistent
`--entry` option. CUDA, native Metal, OpenCL, Vulkan, and ROCm are the implemented
Engine2D runtime adapters.
CUDA font execution uses the separately source-tracked Simple-generated PTX
companion in `backend_cuda_font_ptx.spl`. The default CUDA 2D module contains
no font entry. Canonical CUDA construction verifies the runtime PTX hash, entry,
and program version, then attempts installation through
`Engine2D.install_cuda_font_artifact`. The checker and focused SPipe compare the
pinned source/emitter hashes against the current Simple emitter and currently
fail closed on the recorded mismatch. Once
installed, CUDA uploads the
atlas on generation change, marshals the exact 15-slot pointer ABI,
synchronizes each submitted quad, and mirrors only completed prefixes.
The installer rechecks payload consistency, then delegates to the existing
bounded `install_cuda_font_ptx` entry-symbol/session gate without replacing the
optimization module. The session pins the PTX hash, rejects replacement,
launches font quads from it when present, and unloads it with the CUDA context.
The focused `cuda_generated_font_handoff_spec.spl` authenticates the retained
source-tracked tuple and proves tampered bytes reject, but currently requires
the recorded source/version mismatch and semantics revision 1. Canonical
construction therefore rejects it before installation. After regeneration,
the same scenario must install the pinned identity, dispatch one canonical
`FontRenderBatch`, and compare device-origin readback with its CPU oracle. It is
independent of the Vulkan Engine3D native evidence rows. A retained native PASS
is still required for promotion. If the companion is missing, stale,
rejected, or unsupported by the active driver's PTX ISA, CUDA font dispatch is
unavailable and the existing CPU font fallback applies; primitive CUDA remains
available. Normal Engine2D construction never loads ignored `build/` output.
The current Simple package path is not that trust anchor: `PackageVerify` warns
that checksum verification is skipped, and the package builder still emits
`checksum_placeholder`. Treat checker artifacts as retained evidence only. Do
not copy them into a package, pass their adjacent self-reported hash as trust,
or configure a production process to load them directly. A future external
package route must authenticate its own manifest and bytes before calling the
same installer.
On the current promotion host, a fresh semantics-revision-2 Vulkan candidate
generation attempt is bounded to one invocation:

```sh
SIMPLE_BIN="$PURE_SIMPLE_BIN" SIMPLE_RUNTIME_BIN="$PURE_SIMPLE_BIN" \
  VULKAN_GLSLC_TOOL="$PINNED_GLSLC" \
  PORTABLE_COMPUTE_TARGETS=vulkan \
  PORTABLE_COMPUTE_EXPECTED_SEMANTICS=2 \
  BUILD_DIR=build/portable_compute_toolchains-semantics2 \
  REPORT_PATH=build/portable_compute_toolchains-semantics2/report.md \
  sh scripts/check/check-portable-compute-toolchains.shs
```

Both variable paths must be defined by the operator and name current, admitted
binaries; this host does not currently provide a `PINNED_GLSLC` value. The
authoritative result is
`build/portable_compute_toolchains-semantics2/evidence.env`, not the checker
exit alone. The Vulkan compiler and `spirv-val` run through bounded timeouts,
and the requested-target aggregate ignores unrequested toolchains.
On ELF/glibc hosts, a resolved native-ELF `glslc` candidate runs `--version`
under a clean `LD_DEBUG=libs` loader environment, records the actually initialized
`libshaderc` real path and SHA-256 plus the loader-log SHA-256, and rejects an
operator-supplied `VULKAN_GLSLC_LIBRARY_PATH` mismatch. The exact canonical
GLSL is compiled independently to A/B SPIR-V files; unequal SHA-256 values or
bytes reject the candidate before validation or pin comparison. Other host
loaders fail closed until they have an equivalent tracer; `glslangValidator`
is diagnostic-only and cannot produce an admitted Vulkan font candidate.

Admission has two explicit phases. Candidate generation requires semantics
revision 2, `candidate_compiled=true`, and `artifact_validated=true`, including
`vulkan_font_validator_result=pass` and validator path/version/SHA-256. With
the retained revision-1 pins, the expected result is
`pinned_verified=false`; that is a reviewable candidate, not promotion. After
independent review updates the tracked source/artifact pins and embedded
companion, a fresh run must reproduce the same tuple and set
`pinned_verified=true`. Never update pins merely to make the first run green.
After the reviewed Vulkan pins and embedded companion are updated, rerun with
both `PORTABLE_COMPUTE_TARGETS=vulkan` and
`PORTABLE_COMPUTE_REQUIRE_VERIFIED=1`. Strict mode still writes the
report and `evidence.env`, then exits nonzero unless both candidate validation
and pin verification are true. Its zero-tool predicate check is:

```sh
sh scripts/check/check-portable-compute-toolchains.shs --strict-result-self-test
```

If `PORTABLE_COMPUTE_TARGETS=cuda,vulkan` is requested instead, strict mode
requires validated, pinned companions for both targets.

Metal compiles the exact common MSL helper as an optional separate pipeline,
uses the fixed 13-word/52-byte parameter block, full-uploads changed atlas
generations, and dispatches completed 64-thread groups per quad. Only native
Metal receives the typed batch path; `metal-on-vulkan` remains excluded.
OpenCL `Engine2D.draw_text` uploads the shared atlas when its
generation changes. Its first/reset upload is full; consecutive generations
with valid dirty rectangles use checked per-row buffer offsets, while gaps or
invalid/empty metadata fail safe to a full upload. It then binds the exact
long-scalar ABI, submits one versioned
composite launch per quad, synchronizes, and falls back from the first
unsubmitted quad.

ROCm uses canonical execution target `rocm`; `hip` is an alias in
`FontRenderConfig` identities and plans. Compiler emission and the Engine2D
runtime both consume the exact
`std.common.gpu.font_atlas_composite.font_atlas_composite_hip_source()` text.
The backend compiles that source into its existing HIP module, caches the
versioned entry and atlas by owner/generation, and returns the first
unsubmitted quad for Engine2D CPU replay. Current regressions prove source
identity, invalid/uninitialized rejection, configuration routing, and replay
without AMD hardware. Hosted native builds also compile the optional
`runtime_rocm.c` provider; run
`sh scripts/check/check-runtime-rocm-provider.shs` to validate its HIP/HIPRTC
ABI with local mock libraries. The checker covers UUID identity, module/kernel
launch argument storage, transfers, streams, Engine2D copies, and exact
straight-ARGB transparent/translucent composite pixels. To exercise the public
configured-font route, use an admitted self-host binary:

```bash
PURE_SIMPLE_BIN=bin/release/<triple>/simple \
  sh scripts/check/check-rocm-engine2d-font-readback.shs --mock
PURE_SIMPLE_BIN=bin/release/<triple>/simple \
  sh scripts/check/check-rocm-engine2d-font-readback.shs --real-amd
```

Mock evidence is explicitly non-real. Real mode starts fail-closed, sanitizes
loader variables, requires a root-owned system ROCm provider plus an AMD sysfs
device bound to `amdgpu`, verifies the actually loaded HIP library, and records
compiler, harness, compositor, ROCm-kernel, runtime, native-binary, provider,
driver, and device provenance. Native HIP submission and device-origin pixels
on AMD hardware remain pending until that real-mode record passes; no ROCm
promotion is claimed from source or mock evidence.

`atlas_generation` is a process-unique, positive, sequential dependency token,
not a renderer-local edit count. Each renderer atlas change reserves a token
with an atomic compare-exchange loop. CUDA, OpenCL, Metal, ROCm, and Vulkan pair it
with the batch atlas-owner identity before reusing a backend-local upload.
Concurrent mutation/use of the same renderer remains unsupported. A token gap is safe: OpenCL treats
it as a full upload and uses dirty subrects only for the exact next token.
Sequential means process-local allocation order only; callers must not infer
time or persistence across processes. This closes the bounded atlas-owner and
generation collision, but does not complete REQ-009 or promote native hardware
coverage.

Every `FontRenderBatch` now stamps program version `1`, tied to
`simple_font_atlas_composite_v1_u32`. CUDA, native Metal, OpenCL, and ROCm reject any
other version before atlas/session mutation; Engine2D then replays the CPU
fallback from quad 0. Conditional CUDA/OpenCL evidence covers mismatch
rejection followed by version-1 recovery. ROCm has GPU-less rejection and CPU
replay coverage; Metal currently has static rejection
evidence only because its session has no injectable dispatch seam. None of
this promotes native execution or completes REQ-009 program/backend cache
identity.

Program version 1 is the stable entry ABI; compositor semantics are tracked
separately. The straight-ARGB fix is semantics revision 2. Retained CUDA PTX and
Vulkan SPIR-V are revision 1 and are deliberately rejected until regenerated
through the admitted pure-Simple emitter. Do not update only their embedded
bytes or hashes from a tool-only source reconstruction.

For OpenCL, compiler emission and Engine2D runtime compilation now share the
exact source returned by
`std.common.gpu.font_atlas_composite.font_atlas_composite_opencl_source()`.
The public call remains `Engine2D.draw_text`; direct session/backend launch is
an internal adapter. Font load/unload invalidates the cached atlas identity.
This source path is implemented but not promoted as native evidence until the
conditional device test runs and reports device-origin readback.

Vulkan has a canonical `FontRenderBatch` adapter beside the other Engine2D
adapters. The public Vulkan backend initializes and retains the existing
`VulkanSession`; that one owner supplies the established primitive pipelines,
font pipeline, selected device type, and driver identity. Session initialization
examines the 10,772-byte embedded SPIR-V for
the common GLSL `main` entry (SHA-256
`e25d25b8157fc2554822637603471a442f678eb58e20da167bfb023d7577880a`), but its
semantics revision 1 is stale and installation rejects it before native
resource creation. After regeneration, the same path creates the
zero-push-constant three-buffer pipeline and composites validated quads into
the real device framebuffer. The adapter validates the complete batch before
atlas/cache mutation, binds atlas/destination/52-byte params buffers, waits for
each dispatch, reads the framebuffer directly, and compares it with an
independent CPU oracle, requiring every packed-ARGB `u32` pixel to match. Ordinary unavailable/rejected states replay the CPU
path; unknown fence completion, rollback, descriptor, fence, or resource-cleanup states replace
the Engine2D facade with software and permanently disable that Vulkan font lane.
The conditional integration stops at the first unavailable rung. Promotion now
requires `artifact_mode=precompiled-spirv` with the exact pinned artifact hash;
runtime GLSL can execute but cannot promote. Promotion also requires an accelerated discrete, integrated, or virtual device; a stable
selected device/driver identity; real fenced submission and destruction; direct
device readback; and exact CPU-oracle pixel equality. CPU Vulkan and unfenced submission stop
before mutation and replay through software, so they cannot become native evidence.

Do not add the entry name to metadata alone. Native CUDA/HIP uses a pointer-array
argument ABI, OpenCL needs explicit argument binding, Metal uses the packed
buffer-2 struct, and WGSL uses its own storage bindings. A backend becomes usable
only with matching upload, bind/launch, synchronization, and device readback.

An emitted source string or successful compile proves only emission/compilation.
Native promotion additionally requires nonzero texture/sampler/pipeline handles,
the submitted batch hash, draw/submit evidence, a completed fence,
device-origin readback, a nonblank absolute glyph oracle, and CPU comparison.
Missing hardware is `unavailable`, never a simulated pass.

Hosted neutral shaped runs bind glyph IDs to the exact live face
handle/generation; registered-only runs bind the exact validated blob with
handle/generation `0` and cross Draw IR only as handle-free glyph material.
Both preserve logical codepoint clusters. Those values are not UTF-8 byte
offsets; hosted face liveness or registered-byte identity, plus every parallel
vector length, must match before rasterization.
Their x/y values are baseline pen offsets in device coordinates. The shaper
negates OpenType +Y-up offsets, and `FontRenderer` applies bitmap bearings at
`x = pen_x + bearing_x`, `y = ascent + pen_y - bearing_y - height`. Do not place
raw pen coordinates directly into atlas quads.

## 2D and 3D status

- **2D:** `Engine2D.load_font` and `draw_text` are the supported public surface.
  CUDA attempts its shared versioned atlas-composite path only with the
  verified generated companion; native Metal, OpenCL, and Vulkan attempt their
  corresponding shared path. All retain CPU/image suffix fallback where
  applicable. Other backends retain image-blit compatibility. Source wiring alone is not
  device proof.
- **3D:** `load_font`, `draw_text_hud`, and `draw_text_world` consume the same
  batch through the CPU fallback or optional Vulkan adapter;
  `draw_glyph_run_hud` and `draw_glyph_run_world` do the same for neutral runs.
  Vulkan source owns texture upload/bind, sampler/pipeline, HUD/world transform
  and depth, draw, fence, and device-origin readback. The remaining blocker is
  one retained native run proving those claims; compute dispatch or CPU output
  is not a substitute.

`Engine3D.create_with_backend(..., "vulkan")` installs only the Vulkan font
adapter and honestly reports `backend_name() == "vulkan-font"`; the scene
renderer remains CPU. Repeated installation reuses the live HUD/world pipelines
and sampler. The native source gate compares Engine2D and Engine3D device
name/type/driver tuples, which is a same-device consistency check rather than a
device UUID or retained execution proof.

The Vulkan Engine3D owner now has dedicated HUD and depth-tested world font
pipelines, per-pipeline combined-image-sampler descriptor ownership, R8 atlas
upload, non-indexed draw, fenced completion, and staged device readback.
Graphics recording/submission uses the graphics-family pool/queue rather than
the compute lane. Device selection prefers one graphics+compute queue and uses
it for staging too; transfer-write barriers establish shader/vertex visibility
without an unproved cross-queue handoff. Uploads fail closed, repeated draws use
immutable per-frame vertex buffers released after confirmed completion, and an
unknown fence result retains all submission resources until device idle. The public
Engine3D adapter consumes the canonical batch and keeps CPU rendering only as
fallback or an explicit comparator. Its offscreen font target is still separate
from the CPU scene color/depth target, so world occlusion and native promotion
remain unavailable until a retained device/readback oracle proves the shared
scene behavior; source wiring and validated SPIR-V alone are not device evidence.

The repository also freezes an Engine3D-ready Metal HUD source/vertex contract.
It emits source and packed vertices only; no Engine3D method selects it and it
is not native execution evidence. A rejected runtime draft was removed because
interpreter readback was unsafe, atlas formats were ambiguous, GPU command
errors were ignored, child cleanup was unproven, and the macOS-only code could
not be compiled on this host. Web producers lower through web semantic/layout;
GUI producers lower through canonical widget/scene owners. Both emit Draw IR.
Here `WebIR` means that existing web semantic/layout layer; it is not a second
drawing IR or a place to store glyph, atlas, cache, or native material.
The web semantic style preserves inherited/cascaded `font-family`, including the
`font` shorthand. A successful selected-face resolution records the stable font
identity, exact advances, width, and line height used by layout. Draw IR carries
those semantic style values and, for an accepted shaped run, a handle-free
`DrawIrGlyphRunPayload` containing glyph IDs, positions, and logical clusters;
the payload also round-trips through Draw IR SDN. Engine2D resolves the identity
back to the pinned candidate, verifies the live face generation/identity, then
consumes the shaped payload or applies the serialized advances through the
canonical `FontRenderer`. An absent, unknown, failed, or changed identity
unloads transient vector state and retains the byte-compatible bitmap fallback.
Draw IR never owns face handles, atlas pixels, native resources, or cache state.
Widget Draw IR reuses existing `lang`/`font-family` properties, and shared WM
windows preserve explicit language metadata. Missing language remains `und`
and keeps the prior Noto Sans Mono default; explicit multilingual text without
a family selects the accepted sans face for its language.

The unused famous-site fixture fallback and its browser-private atlas compositor
were removed; active host web text and the production Simple Browser use the
existing HTML -> `DrawIrComposition` -> Engine2D route. The guest entry registers
exact validated VFS bytes with the existing `FontRenderer` before layout and
requires all 16 candidates before rendering; it never calls the browser-private
software-pixel renderer. Remaining explicitly
compatibility-only framebuffer fixtures may still rasterize 5×7 glyphs.
Widget/GUI and shared-WM composition builders use their canonical semantic/scene
owners. The canonical SimpleOS desktop executes that composition through
`Engine2dWmFrameExecutor`; canonical ARM64/x86_64 runner/readiness targets now
select `gui_entry_desktop.spl`. Direct legacy `wm_entry.spl` files still contain
bitmap text but are compatibility-only, not production-route evidence. Hosted
`_run_hosted_wm` retains one persistent `Engine2dCompositorBackend` and passes
it to `HostCompositor.render_frame_engine2d`, which executes `SharedWmScene ->
DrawIrComposition -> Engine2D`. This source route is not executable/device proof; the programmatic
direct-compatibility gate, image/motion backgrounds, nested content, and
rejected-readback retries remain non-completion paths. Do not add a paint-local
loader, atlas, cache, or private font draw path.

SimpleOS image construction now iterates the closed 53-entry OS projection
described above. Installer rootfs, initramfs, and pure-Simple nested FAT32
staging validate each immutable source against its pinned SHA-256; root
`LICENSE` and `THIRD_PARTY_NOTICES.md` are nonempty transport-owned inputs. The
16 TTFs retain their readable registry-owned VFAT long names and unique 8.3
compatibility aliases, while provenance and legal companions use collision-free
8.3 names below `/SYS/FONTS`. The canonical `/assets/fonts/...` TTF value remains
the identity. The pure-Simple image writer emits LFN slots and the shared reader
resolves them before its raw 8.3 fallback. Pure-Simple path readers retain a
bounded 32 MiB ceiling, above the largest pinned 25,125,512-byte face; the live
x86_64 and ARM64 C bridges use the same cap. This adds 28 MiB of static `.bss`
to the selected architecture's kernel image. The Simple Browser
accepts only validated registered TTF bytes and rejects any skipped Draw IR
command. Missing or changed assets cannot become a selected vector face.
Registered-only source paths bind the exact validated Arabic/Devanagari blobs
to the existing pure-Simple shaper with handle/generation `0`, emit only
handle-free glyph payloads, and materialize them through the existing
selected-byte renderer. Retained guest/QEMU pixels remain pending; packaging
and a host-side image hash are not guest rendering evidence.
The pure-Simple builders own the canonical path. The still-live C image writer
mirrors the readable names and fixed short aliases for compatibility with its
existing toolchain/evidence image callers.
On AArch64 the canonical desktop source route attaches that existing VirtIO-BLK
FAT32 image, resets stale VFS state, and attempts to mount it and register the
selected catalog before Engine2D creation. A failed mount or post-mount
executable probe clears VFS readiness. Host image acceptance requires `mtype` extraction plus
an exact 1,708,408-byte SHA-256 check; missing tools fail closed. RV64 remains
on its existing bitmap path because the initializer is ARM-only and the current
64 KiB runtime heap cannot carry this vector-font bootstrap. Both canonical ARM
scenario contracts require the exact successful registration marker; bitmap
fallback cannot satisfy them.
The x86_64 SimpleOS witness is the existing 12 px `taskbar-clock` command in the
real `SharedWmScene -> DrawIrComposition -> Engine2D` frame; the private
post-frame `A`/32 px draw was deleted. The fullscreen QEMU wrapper is configured
to capture the dynamic rightmost 56x48 slot (8,064 RGB bytes), and retained
consumers require the canonical wrapper, kernel ELF, and FAT32 image paths with
independently recomputed SHA-256 values. No current retained guest/`pmemsave`
PASS bundle proves the crop, so REQ-011 pixel promotion remains unavailable.
Do not add another font draw path or reuse Engine3D HUD/world.

## Completion workflow

Keep the remaining work on the frozen public seams:

1. `FontRenderer` prepares metrics, shaped runs, and `FontRenderBatch`.
2. Web/GUI/WM producers emit semantic `DrawIrComposition`; Engine2D alone
   materializes vector glyphs and retains bitmap fallback.
3. Selected Latin, Han, exact Hindi, exact Arabic/Urdu, and Cyrillic fixtures must
   prove face, glyph, cluster, advance, offset, direction, language, and script
   identity before a matrix cell is accepted.
4. Engine3D HUD/world promotion requires texture, sampler, pipeline, draw,
   completed fence, depth/transform behavior, and device-origin readback.
5. SimpleOS proof names the packaged candidate/hash and checks literal guest
   framebuffer pixels. Pixelify Sans separately must execute its pinned literal
   default-axis dimensions/advance/checksum oracle.
6. Warm performance records cache hit rate and 1,024-glyph p95 at 1080p/4K;
   promotion also records equal-semantics 4,096-glyph CPU/GPU p95, unchanged
   upload behavior, RSS delta, and GPU resource high-water. Durable schema v5
   also pins viewport, byte-domain packed-ARGB/straight-alpha and rounding
   semantics, per-route warmup, percentile policy, exact packed-ARGB CPU-oracle
   comparison, same-host OS/architecture, and device/driver; FNV64 remains a
   runtime diagnostic and any field drift fails closed. The same record requires
   controlled Vulkan-poison CPU fallback, unchanged prepared-batch identity, and
   eleven post-loss CPU samples whose p95 does not exceed the baseline CPU row.
   It also retains one emission/compile-install scalar and seven 11-sample
   stage arrays for shaping, material, unchanged dirty upload, fused
   submit-through-device-completion `queue_device`, later fence observation,
   offscreen device readback, and CPU oracle. The fused and fence-observation
   intervals overlap and are never summed. `not-applicable-offscreen` records
   the absence of swapchain present, not the absence of required readback.

Production-route acceptance must exercise the real Web/GUI entry, the hosted
`HostCompositor` canonical color-frame owner, and the canonical SimpleOS desktop
entry. Current hosted coverage is a source/unit contract, not a production-route
PASS; image/motion and nested content remain compatibility cases. A synthetic
composition-only spec is supporting evidence, not production proof. SimpleOS
acceptance additionally requires the retained QEMU `pmemsave` pixel oracle.
The shared host Web renderer now routes both pixel and readback requests through
the existing HTML-to-DrawIR Engine2D entry; its heuristic renderer remains only
as an explicit compatibility oracle.
`ui.browser` now prepares one canonical `widget_tree_to_draw_ir` composition
and executes it through Engine2D for pure-Simple pixels. The private widget
command list is deleted; Chromium remains an explicit compatibility renderer.
Queue dispatch stays `not_requested` until the composition itself is submitted;
a separate frame event cannot be labeled as Draw IR dispatch evidence.
The artifact retains the executor's exact readback source (`cpu_mirror`,
`device_readback`, or the backend's other explicit source) without normalization.

Vulkan device-loss or unknown completion poisons only the Vulkan surface. When
policy permits CPU, Engine2D replays the same immutable `FontRenderBatch` from
quad zero through the replacement software surface; required GPU-only policy
still fails closed. The v5 source gate retains post-loss CPU p95 and identity;
native device-loss injection remains the NFR-007 execution gate.

Keep the five primary SSpec steps exact: `Load the pinned multilingual
font manifest`; `Accept exact-face-bound simple-script shaping`; `Prepare one
shared font batch for 2D and 3D`; `Emit the selected font composite program and
plan compilation`; `Prove native submission and device readback`. Resolved-host,
completion, and folded secondary detail steps use the vocabulary recorded in
the authoritative system-test plan below.

The authoritative gate list and evidence boundaries are in
[`doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`](../../03_plan/sys_test/shared_multilingual_gpu_fonts.md).
Run focused acceptance evidence natively with the self-hosted CLI, for example:

```bash
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl --mode=native
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl --mode=native
```

For each of the 11 pairs in the authoritative plan, generate its mirrored
scenario manual after that executable spec passes with
`bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`. Accept the
manual only when docgen reports completion with `0 stubs`, it reads as a useful
operator manual, and `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

Interpreter runs are diagnostics only. These native source gates still do not
substitute for submission, SimpleOS pixel, Engine3D, or performance gates.

A focused runner invoking a selected pure-Simple runtime is trustworthy only
when its wrapper checks `get_executed_test_count` and `get_exit_code` inside the
interpreted source;
`CompileResult.Success` by itself is false green for matcher failures. The fail
fixture must exit 1 with `test-runner: spec failed`; the empty fixture must exit
1 with `test-runner: no examples executed`. Reject 2/124/139 and retain exact
commands, runner SHA-256, and both logs under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
The result may be labeled only
`interpret-diagnostic`; it cannot promote manifest, native GPU, SimpleOS pixel,
Engine3D, or performance evidence. Use the two calibration fixtures under
`scripts/check/fixtures/font_evidence_runner_{fail,empty}_spec.spl`.
The pure runner and focused runner share
`std.test_runner.test_result_wrapper.build_interpreter_result_wrapper`; do not
fork another harness or bypass its summary and fail-closed checks.
Pass the exact admitted pure-Simple CLI as the focused runner's first argument;
the second argument is the spec path. It deliberately has no implicit binary
fallback. The runner preserves child stdout/stderr, maps only an explicit
timeout marker to 124, and reports launch failure as 1.

Run each acceptance gate once per session. Unavailable hardware or the stale
self-hosted runtime is a blocker record, never a synthetic PASS.

## Evidence rules

Check structured batch/DrawIR/object state before pixels. Native evidence must
identify the actual backend and readback origin. Pixel equality, upload-only
records, emitted code, environment-published payloads, and CPU mirrors cannot
independently prove GPU execution.

See the [architecture](../../04_architecture/shared_multilingual_gpu_fonts.md),
[design](../../05_design/shared_multilingual_gpu_fonts.md), and
[requirements](../../02_requirements/feature/shared_multilingual_gpu_fonts.md).

Selected bundled faces resolve the native-only raster ABI. A zero native
handle composes with the retained-byte common cmap/glyf rasterizer; unmanaged
faces retain the legacy native-plus-fontdue ABI. Focused native tests force a
real native miss while proving the legacy raster remains successful, and the
common raster tests independently prove successful outline output.
