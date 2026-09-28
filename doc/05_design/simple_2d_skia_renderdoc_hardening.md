<!-- codex-design -->
# Hardening detail design — selected C/N2

Status: selected by the user on 2026-09-26. Names below are coordination contracts until their implementations and tests are reviewed. Physical Linux Vulkan qualification remains open.

Proposed evidence presentations are in
`simple_2d_skia_renderdoc_hardening_gui.md` and
`simple_2d_skia_renderdoc_hardening_tui.md`. They display typed receipts and
completed pixels; neither is an implemented application screen.

## Bridge preflight

Proposed `skia_picture_engine2d_preflight(picture)` checks every operation and the paint/geometry semantics actually consumed by the bridge. Reject unsupported paths/text/points, ignored shaders/blend/stroke, unpreserved fractional coordinates, invalid extents and unsupported unequal elliptical radii. Do not reject semantically equivalent no-op state unnecessarily. Report the first operation index and concrete reason. Strict entrypoint `skia_render_picture_on_engine2d_strict` returns a Result and calls rendering only after successful preflight. Keep rendering inline where the documented interpreter mutation behavior requires it.

The current Engine2D uniform rounded-rectangle emulation emits fractional
corner coverage regardless of the picture paint's antialias flag. Until an
operation-level path can honor both paint modes, strict preflight rejects a
nonzero rounded radius. The reported preview may still show the approximation
with `complete=false` and `rrect-coverage-anti-alias` in its receipt.

Extend existing `BridgeReport` with `complete`, `reason`, `lossy` while retaining mapped/skipped counters. Successful strict output requires complete=true and zero skipped/lossy operations. Preview output must carry incomplete evidence when any semantic loss occurs. Pixels-only compatibility API is not an admission oracle.

## Capture admission

v1 `outputSha256` remains the encoded PNG integrity domain. Validate digest syntax and actual graphics evidence at parser entry even for hand-authored input; no empty strings or error strings can compare as valid output. Normalize hexadecimal case if accepted in both cases. Validation must also protect callers constructing event sets directly if alignment is public.

A future version extends existing common render records with explicit final resource/subresource, completion token, dimensions/stride, format, alpha, transfer/primaries, origin/crop and canonical decoded pixel hash. Hashing binds metadata and pixel bytes. Ambiguous output or unsupported conversion returns CAPTURE_ERROR; missing device returns BLOCKED_ENVIRONMENT; incomplete output returns INCOMPLETE_FRAME; semantic/pixel differences remain distinct. Compute-only valid frames require final-resource capture, not invented graphics attachments.

## Reproduction and test flow

Shared manual steps: `step("Load the pinned scene")`, `step("Preflight the complete picture")`, `step("Render the completed frame")`, `step("Validate capture provenance")`, `step("Compare canonical final pixels")`.

Shared proposed helpers: `setup_pinned_scene`, `check_preflight_rejection`, `check_complete_frame`, `check_capture_provenance`, `check_canonical_pixels`. Unimplemented executable helpers must fail with `assert(false)` or a concrete `fail(...)`; never generate passing placeholder manuals.

Selected requirements will map to strict unsupported-after-valid-op rejection before dispatch; fractional/paint loss receipt; valid and malformed digests; compute-only v1 blocking; explicit final-target completion; serialization round-trip; web and GUI input parity; independent primitive oracle. Generate manual evidence only from executable scenarios. Store screenshot/diff assets under `doc/06_spec/image/` and operational captures under `build/test-artifacts/`.

## Native prototype admission

Choose pinned Skia revision before build integration; compile against matching headers/features. First prove device/context construction, teardown, wrong-thread/device-loss and completed readback. External VkImage/presentation admission follows queue-family, layout, semaphore and resolve tests. A C-header syntax check does not qualify this provider.

## Current C/N2 integration boundaries

The shared DrawIR v3 fractional payload is now produced and preserved through
`UiIr`. The Engine2D strict Vulkan primitive lane is being extended with a
defined non-antialiased rectangle rule: pixel `(i, j)` is covered when its
center `(i+0.5, j+0.5)` lies inside the authoritative half-open f64 rectangle.
The first opaque full-surface clear remains integer-only. This rule must pass a
real device pixel comparison before it is qualified; integer-only damage and
generic executor routes continue to reject fractional commands.

The upstream Skia provider currently admits one untransformed batch of plain
filled rectangles. This is a controlled primitive slice, not Web/GUI corpus
coverage. Web producer completeness (`render_degraded`, reason, assets and
state) must be retained alongside its composition. GUI input and widget state
must be retained likewise. Do not drop unsupported command semantics or
promote a rectangle-only comparison to the 48-case corpus.

### Web decimal geometry and transform gate

Corpus case `02-fractional-edges` combines decimal box offsets and dimensions
with `translate(.25px,.25px) rotate(7deg)`. The current Web declaration path
stores `width`, `height`, `left`, and `top` as `i32`; it folds translation into
integer offsets and handles only quarter-turn rotation. Its resulting DrawIR
cannot prove this page's authored geometry. Do not qualify case 02 by
projecting those integer boxes through the rectangle-only provider.

The next reusable producer increment must retain resolved f64 box geometry
before integer layout compatibility fields discard precision. For supported
identity or translation-only absolute boxes, Web DrawIR emits authoritative
`fractional_geometry`, preserves the source command index and clip space,
and `draw_ir_to_ui_ir` carries the same values. Unresolved rotation, scale,
skew, perspective, or origin-dependent transform returns a typed admission
failure before GPU submission. The existing non-antialiased pixel-center rule
remains the only admitted fractional raster policy until an explicit AA policy
and fixture-specific tolerance are implemented.

An initial provenance guard now retains normalized raw `transform`,
`translate`, `scale`, and `rotate` declarations on each computed Web Style and
source DrawIR command. The rectangle-only admissions require all four to be
`none`. This prevents those paths from silently accepting a transformed
command after the current integer declaration handling folds or ignores its
geometry. The real-producer regression spec is present but unexecuted; this
guard does not preserve decimal box coordinates or implement affine raster.

Astra's declaration-path review (2026-09-26) found that a command-only
decimal check cannot close this gap. The full declaration path truncates
`left`/`top` and `width`/`height`; the fast dispatch path independently
truncates `width`/`height`. Integer visibility culling can then omit a
subpixel box before any DrawIR command exists. The rejection-only producer
change now captures authored tokens before either integer parser, keeps them
through Style copying and layout Style reconstruction, and computes an
unresolved-geometry scene verdict before visibility culling.
The rectangle admission may accept only a fully parsed integer `px` token or
unitless zero for an explicit length; decimal syntax, expressions, other
units, and unresolved keywords fail closed until f64 geometry is available.
The guard must account for `inset`, logical inset and sizing properties,
`right`/`bottom`, min/max constraints, and containing-block ancestors: an
integer-looking child is not safe if an ancestor's position was rounded.
Later same-property declarations replace their prior token; competing
shorthand and constraint tokens remain conservatively blocking. Border side
and logical shorthands are captured; legacy `clip` fails closed. The focused
real-producer spec is written but unexecuted under the verifier cap. This is
a rejection boundary, not evidence that Web preserves fractional geometry.

The implemented, unverified producer mode uses a separate
`simple_web_layout_render_html_draw_ir_fractional_result` producer mode that
shares parsing, cascade and layout while emitting authoritative DrawIR v3
fractional rectangles. An internal
`web_resolve_absolute_px_leaf_boxes(nodes, styles, boxes, viewport)` returns
optional f64 geometry per node and one scene rejection reason. Its first
admitted shape is an opaque absolute leaf with explicit finite decimal `px`
`left`/`top`/`width`/`height`, border-box sizing, zero box decorations and
effects, and an integer, untransformed immediate containing block. It rejects
competing inset, logical sizing, right/bottom, min/max, transforms, animation,
scrolling, sticky/fixed positioning, intrinsic-size dependence, and fractional
or transformed ancestors. Clips must be viewport-equivalent, and the entire
f64 rectangle must fit within them. Coordinates are parent border-box origin
plus parsed offsets; dimensions come directly from the winning raw tokens,
never from rounded child layout fields. Finite positive extents and derived
edges are required. Decimal CSS is parsed into f64; the binary conversion is
the transport contract, not an assertion of exact decimal representation.

The resolver runs before integer visibility culling, and admitted fractional
leaves use f64 visibility so `0.5px` extents survive. Their DrawIR commands
carry `fractional_geometry` with zero legacy integer fields and retain source
node/component identity; integer border/content/hit rectangles do not stand
in for fractional bounds. Existing CPU execution rejects these commands until
its own semantics are implemented. Focused tests must prove fast/full cascade
parity, same-property override, nonzero parent origin, subpixel visibility,
DrawIR/SDN/UiIr f64 preservation, unsupported ancestor rejection and explicit
CPU rejection. This mode can emit case 02's untransformed narrow bar; the
rotated tile still blocks complete case 02 qualification.

The mode now captures every applied authored declaration for a strict
property/value allowlist and rejects unsupported paint such as filters, masks,
blend modes and list markers. It rejects pseudo-element selectors, linked or
imported stylesheets, scrolling and animation before emitting a batch. A
rejected result carries `fractional_scene_rejection_reason` and zero batches.
The focused real-producer spec is written, but no trustworthy Simple runtime
PASS exists yet; physical Vulkan comparison is also outstanding.

### Case 02 affine and coverage contract (Astra + backend reviews)

The implemented, runtime-unverified shared schema is DrawIR v4 with optional `DrawIrAffine2D(a,b,c,d,tx,ty)`
and explicit `aliased-pixel-center` or `coverage-aa` raster policy. An affine
command has local f64 rectangle `(0,0,width,height)` and zero legacy integer
coordinates. Its surface point is `(a*x+c*y+tx,b*x+d*y+ty)`. A nil matrix is
identity. V3 SDN promotion supplies identity and its existing pixel-center
policy; v4 deserialization validates finite coefficients, dimensions, clip and
policy before returning executable commands. UiIr preserves all of these;
older executors reject the whole composition before dispatch.

The v4 constructors, SDN transport and checked parser, UiIr v2 lowering, and
audited rejection paths now exist. The Web case 02 source producer, Engine2D
affine-coverage candidate, Skia private v3 wire validator, and independent
polygon oracle also exist in source. Focused specs have not run through a
trustworthy Simple executable; native Skia affine rendering remains disabled.

For the pinned tile, width is `180.5`, height is `100`, and the default local
transform origin is `(90.25,50)`. CSS requires
`M = T(40.25,50.5)·T(90.25,50)·T(.25,.25)·R(7°)·T(-90.25,-50)`.
With screen coordinates and positive CSS rotation,
`a=d=cos(7°)`, `b=sin(7°)`, `c=-sin(7°)`, and approximately
`tx=47.26617698462807`, `ty=40.123984175619334`. The bar uses local
`(0,0,2.5,280.5)` with translation `(290.5,40.25)`. Web resolves these from
the winning CSS tokens and retains source node indexes. The painted white
`#scene`, its `overflow:hidden` viewport clip, both leaves, and canvas must
all survive source admission; current single-leaf/transparent-parent rules
must not silently drop them. Clips are in surface coordinates and apply before
each local matrix. Source IR remains CPU-provenance; the GPU adapter changes
target only after complete scene preflight.

Case 02 requires `coverage-aa`; the existing non-AA pixel-center rule cannot
stand in for rotated browser edges. The independent oracle clips each
transformed polygon against each pixel square and computes the bar's
fractional area over white. Exact interior and untouched exterior pixels are
separate assertions. Edge tolerance, premultiplication, compositing color
space, transfer function and f64-to-SkScalar conversion bounds must be pinned
in the fixture manifest before viewing either GPU capture. The current
manifest pins the independent polygon oracle and edge tolerance but has no
completed case 02 GPU reference bytes, so no parity verdict is available.
Approximate backend agreement alone is insufficient.

Engine2D needs a new strict Vulkan affine coverage pipeline: its current
integer rectangle shader and host `draw_image_transform` cannot qualify.
Avoid diagonal seams or double blending between quad triangles; preserve the
existing submit/fence/readback and device UUID evidence. The Skia provider
uses a private v3 payload carrying local f64 rect, six coefficients, coverage
policy and surface clip; private v1/v2 remain byte-stable. Its native draw
sequence is save, set surface clip, concatenate matrix, draw local rect with
AA, restore. Both backends preflight all records and transformed bounds before
resource creation, and reject partial scenes. Tests cover transform order and
origin, parent offset, clip ordering, invalid/singular matrix, SDN/UiIr
round-trip, edge coverage, diagonal seam, source mapping and complete case 02
inventory. Trusted build and physical Linux Vulkan captures remain gates.

The private v3 header and CPU validator now pin a 128-byte record, finite and
invertible submitted f32 matrix, bounded target clip, and at most 0.125 pixel
transformed-corner conversion error. The default Simple and native entrypoints
still reject v3. Separate candidate entrypoints and an explicit native build
opt-in exist, but submitted-matrix provenance, pinned-header compilation and
physical pixel validation remain open. This is not Ganesh qualification.

## GUI visible input text admission

`gui_input_qualified_states` already delivers a real click and the key sequence
`A`, `B`, left, `C`; it checks the resulting `ACB` value, caret index 2, and
different before/after widget DrawIR. That proves source state, not glyph
pixels. The physical runner currently admits GUI button states only. Engine2D
has a strict Vulkan text execution path, but its owner, font, submission and
readback evidence have not been qualified for this input scene. The upstream
Skia Simple preflight and native private wire accept rectangles only.

For this one scene, the source gate now pins bundled Noto Sans Mono bytes by
SHA-256 and requires its resolved identity, complete glyph arrays and bounded
caret geometry. Exact per-glyph visual positions, raster configuration and
physical text pixels still need independent admission. Keep the original text commands in shared
DrawIR; do not reinterpret a 5×7 charset glyph index as a vector font glyph
ID. A future native text record needs its own versioned private format and
whole-composition preflight; v1/v2 rectangle bytes and v3 affine bytes stay
unchanged. It must consume a bounded resolved glyph subset with the pinned
font and reject mismatched font identity, unsupported shaping, clipping,
blend or effects before device work. Engine2D must prove its existing strict
text path used the same admitted font input without CPU framebuffer fallback.

Add separate before/after prepared scenes, two backend capture adapters and
fresh worker commands only after that font contract exists. Each receipt
binds source state, both DrawIR digests, font digest, executable/provider
digests, selected device UUIDs, final resource, completion and pixel domain.
An oracle prepared independently of both submitted DrawIR and backend
lowering checks the text and caret regions of each state, with any font edge
tolerance declared before seeing device captures. Pairwise backend agreement
alone cannot admit missing glyphs. Until both physical captures pass, this
scene remains source-qualified and device-blocked.

The direct `SkPicture` producer admits only nonempty, full-surface recordings
with an opaque integer full-surface first rectangle, followed by bounded,
non-antialiased SrcOver filled rectangles. It scans every operation before
constructing DrawIR, rejects a different recording cull, and retains f64
geometry. The upstream Skia provider now applies the same initializer,
opacity, bounds, and GPU-target rules as Engine2D's controlled rectangle path.
Each backend still performs its own complete preflight before device work.

The physical qualification contract currently validates supplied capture
metadata but has no trusted adapter that obtains resource identity, completion
correlation, pixel domain and physical device properties from both backend
owners. A caller-provided device name or `producer_authenticated` boolean is
not independent device proof. Until those adapters and a Linux capture run
exist, the result is structural/offline evidence only; NFR-2D-002 remains open.
The pair contract requires matching Vulkan device and driver UUIDs in addition
to name/type/driver labels. Engine2D's current runtime exposes only a
device-present sentinel and the Skia provider exposes an enumeration index;
neither value identifies hardware across processes. Each backend
owner must query `VkPhysicalDeviceIDProperties` for its selected physical
device and bind those UUIDs to the completed capture; caller strings alone
still produce only a candidate.

### Native UUID provenance extension (Astra review, 2026-09-26)

Keep `SimpleGpuProviderAbiV1` and `SimpleGpuReceiptV1` byte-compatible. An
optional versioned provider export returns a fixed-size identity record for a
specific live session **and completion**. Its fields include `struct_size`,
version, raw 16-byte device/driver UUIDs, vendor/device IDs, device type, API
version, and driver version. The optional Skia owner queries
`VkPhysicalDeviceIDProperties` during creation of its selected `VkPhysicalDevice`
and retains those immutable facts in that session. Its export refuses a
completion that has not reached waited/readback-ready state.

`runtime_dynload.c` resolves this export only from the already authenticated
provider handle. Its host entrypoint requires an owned, nonquarantined,
terminal completion with observed readback, translates host tokens to native
handles, and pins both the module and session during the call. A missing
extension means unavailable UUID evidence, while ABI-v1 providers continue
to load normally. Copy the identity into the Skia frame before releasing the
completion and session; encode each UUID byte as two lowercase hex digits.

Engine2D's `VulkanSession.physical_device` is a placeholder. Its actual native
Vulkan owner exposes an identity query through the SFFI facade that requires
the completed submission's selected-device generation token. The native query
checks that token under the state lock before reading the selected physical
device's UUIDs. A process-global query without that token could name a
different session and cannot qualify N2. The deployed symbol route and
physical Linux behavior still need verification. No API path may accept
caller-constructed UUIDs as a physical PASS.
Engine2D strict Vulkan submissions now carry the completed fence generation
through readback. The readback path rejects a changed generation, framebuffer,
device, or incomplete frame receipt before returning pixels. This links one
submission to its readback within the Engine2D owner. The owner-bound UUID
query supplies selected physical-device identity; independent process and
external final-image provenance still require the Linux qualification runner.
The controlled fixture pins ARGB8888 source colors, opaque non-antialiased
coverage, top-left origin, and sRGB primaries/transfer. The Engine2D capture
adapter takes extent from the linked Engine2D owner, rejects nonopaque alpha,
and converts checked packed words to RGBA bytes; the Skia capture adapter
records its explicit RGBA readback. Physical session provenance is still open.
The canonical pixel validator rejects an `opaque` RGBA claim if any raw image
pixel has an alpha byte other than 255; padding bytes are outside that rule.
The Web corpus producer receipt marks UiIr rejection, command loss, missing
required image commands, unverified inline SVG semantics, fractional CSS
geometry, transform raster semantics, or an unapplied nested scroll state as
blocked cases. It derives required features from the
manifest and records the emitted image-command count, so a page background
cannot stand in for missing source content. Cases 29 and 30 bind the
hash-checked checker SVG's authored 80 × 80 RGBA
derivative; the receipt records source and derivative digests without claiming
general SVG decoding. The GUI input scenario requires
both CPU frame artifacts to be
written before it records their filenames. Neither receipt is Vulkan proof.
The element-scroll producer resolves a selected scrollport by ID, computes
extent from raw content rather than its border, translates descendants, and
keeps the raw layout for source evidence. It rejects a viewport-fixed
descendant explicitly because that element needs a separate containing-block
placement rule. The focused scenario checks a border-only no-range case and
this fixed-descendant rejection.

## Dual-backend Web and GUI semantic expansion

The pinned 48-case Web corpus covers more than the current Skia provider's
opaque rectangle subset. Keep `DrawIrComposition -> draw_ir_to_ui_ir -> UiIr`
as the shared contract and add a private, versioned provider payload. The
payload must declare total length, bounded command and resource sections,
typed operations, and balanced clip/layer state. Native code validates the
entire payload before allocating GPU work. CSS strings are resolved to typed
drawing semantics before the provider boundary; unsupported fields reject
the complete scene rather than disappearing during lowering.

| Stage | Shared semantics | Native work and evidence |
|---|---|---|
| 1 | Real Web/GUI opaque boxes, borders, rectangular clips and translation | Private v2 clip/rectangle commands; source producer, both backends and exact pixel oracle on pinned box-only fixtures |
| 2 | Resolved text and image resources with pinned font/asset hashes | Ganesh glyph placement and image upload; shaping, sampling, alpha and lifetime evidence |
| 3 | Paths, strokes, corners, gradients and transforms | Typed operation parity and independent primitive oracles |
| 4 | Opacity groups, blends, filters, masks and backdrop inputs | Layer/effect ordering, bounds and completion evidence |

The GUI source spec now checks an unlabeled button's resting and pressed
DrawIR through the rectangle-only Skia preflight and verifies that CPU and
GPU-targeted producers expose the same changed fill. This is an input-path
slice: labeled text, native execution, and completed pixel evidence remain
open. The full GUI scene cannot be admitted from preflight alone.

The pinned `gui-button-16x16-v1` scene uses the real widget layout producer
with an explicit opaque theme snapshot. The themed producer emits a full-target
surface initializer followed by the unlabeled button rectangle; its normal
and pressed colors resolve from `wm.controls` and `workbench.tab_bar`. Its
focused spec checks both complete GPU compositions through UiIr and Skia
preflight. The theme digest binds widget ID, extent, colors and normalized
material; fixed expected input digests bind button ID, label, action, and
each pressed state. The source scene does not
yet have a completed physical Engine2D/Skia capture or a trustworthy Simple
test result. An independent two-state pixel oracle and Linux candidate runner
are present.

Each corpus row tracks producer state, lowering, Engine2D and Skia execution,
assets/fonts, declared tolerance, oracle, and physical capture. A first-stage
box result cannot close the remaining text, image, SVG or effect cases; all 48
remain open until their actual semantics execute through both Vulkan routes.

The pinned `web_opaque_box_v1.html` is a first Web source fixture. Its focused
producer spec binds the exact HTML bytes, checks the resolved `#box` layout and
opaque color, retains computed style, and confirms the original CPU-targeted
composition remains outside strict Vulkan admission. The new Stage 1 lowerer
checks producer state, all fixed style keys, raw paint state, clips, geometry
and ordering before deriving GPU rectangles from the producer's own values.
It retains the original DrawIR digest and command-to-source indexes; unknown
effects reject. Its positive admission and Skia preflight spec has not run, so
the source path is not yet qualified. A hardcoded rectangle scene or ignored
style field would not qualify as Web execution evidence.
An independent 16 × 16 RGBA oracle binds that HTML digest and expects the
authored background plus the 8 × 8 blue box. It can reject two matching but
wrong backend outputs; it cannot qualify the scene without admitted lowering
and completed physical readbacks.
The Linux `run-web-box` runner now submits the lowerer's actual GPU DrawIR to
isolated Engine2D and Skia workers. Candidate receipts bind the pinned HTML,
original and GPU DrawIR digests, source command mapping, device UUIDs, and
oracle-checked RGBA bytes. The focused negative spec and offline
`verify-web-box` path cannot establish a physical pass; neither the positive
Simple spec nor a Linux GPU capture has completed here.

Corpus case `01-solid-boxes` now has a separate pinned 640 × 480 admission
path. It retains the real Web producer's command identities and paint order,
checks the full-target `#scene` overflow clip, and derives GPU rectangles
from producer values. An independent oracle pins the source HTML, SVG
reference, and exact white/red/blue/green pixels. The expected seven-command
producer inventory and both physical captures remain unverified; this case
does not promote the other 47 corpus rows.

Corpus case `06-rectangular-clip` has a second source-bound Stage 1 path. Its
authored overflow parent clips a larger cyan child to x80..199, y65..139.
The independent HTML reference and RGBA oracle pin this visible result;
admission must retain the producer's actual child geometry and parent clip.
The dual-backend runner has separate case 06 owner adapters and receipt pins.
Actual producer command inventory, Simple execution, and physical GPU output
remain unverified. The other 46 corpus rows are still unqualified.

The first Stage 1 increment now has a private v2 rectangle record with a
target-coordinate clip, selected only when a command carries a clip. The
existing v1 record remains the no-clip format. Admission rejects malformed
clip dimensions and values that SkScalar would round. Native validation runs
before drawing, and each clip is scoped to one rectangle. This is source and
static-header evidence only: the pinned Skia build, real Web/GUI source
admissions, and physical dual-backend captures remain unverified.
Engine2D's strict Vulkan rectangle path now computes the exact integer
intersection of the command rectangle, command clip, and target in `i64`, then
dispatches only the visible opaque rectangle. Empty intersections process as
zero coverage. This keeps GPU work bounded by the target and does not carry
clip state into the following command. The corresponding pure geometry spec
is present but has no trustworthy Simple runtime PASS yet.
The paired clip matrix uses only integer coordinates exactly representable as
SkScalar: Skia rejects lossy integer-to-`f32` values, while Engine2D can keep
them as integers. Skia also accepts some fractional clipped rectangles that
the current strict Engine2D clip path rejects. Neither difference may be
silently called parity; fractional clipped geometry remains a later stage.
The controlled clip fixture and independent analytic oracle now pin one
16 × 16 pixel scene with visible, empty, disjoint, and later unclipped draws.
The Linux qualification CLI has a separate `run-clip` path and candidate-only
`verify-clip` path. These are executable source paths without a trustworthy
Simple compile or physical device run in this workspace.
