<!-- codex-design -->
# Image-to-Markdown Multimodal Pipeline Detail Design

## Scope

This design implements the approved pipeline from image input to deterministic
Markdown, canonical structured document, and synchronized evidence receipt. It
includes Caret/Slang multimodal transport, local/API profile settings, SPipe
action wiring, and the discoverable Codex `image-read` skill. It does not add a
GUI, train a model, translate text, or treat inference as an expected oracle.

## Public contracts

The implemented versioned contracts are:

```text
ContentPartV1
MultimodalMessageV1
MultimodalRequestV1
VisionCapabilitiesV1
ModelProfileV1
ModelCompletionV1
MultimodalErrorV1

ExtractionDocumentV1
ExtractionRegionV1
SourceBoundsV1
TextSpanV1
TableV1 / TableCellV1
ChartPanelV1 / ChartSeriesV1 / ChartPointV1
ExtractionReceiptV1
ExtractionArtifactsV1
```

`ContentPartV1` is a closed flattened boundary: `kind=text` carries
`text_content`; `kind=image` carries the admitted artifact ID, MIME, dimensions,
SHA-256, detail, and transient data URL. `text_part_v1`, `image_part_v1`, and
`image_data_part_v1` are the canonical constructors. Existing text-only Caret
messages remain unchanged.

`complete_multimodal_v1(request, secret, cli_path, system_prompt)` is the only
extraction-to-Caret provider call. The orchestrator injects that completion
function for deterministic testing. Values have value semantics; no contract
retains an open stream, mutable provider client, secret, or unowned image
buffer.

## Data rules

### Images and bounds

`SourceBoundsV1` uses integer pixel coordinates `(x, y, width, height)` in the
admitted source coordinate space and records page index. The initial PNG path
records preprocessing as `none/1`; it does not claim orientation normalization.
Coordinates are half-open and must remain inside page dimensions.

Supported initial MIME types are allowlisted by decoder capability. MIME is
verified from decoded content, not trusted from filename. Decoded byte/pixel
limits are checked before large downstream allocation.

### Text, handwriting, and annotations

Every span stores source text, reading order, bounds, confidence, detected
script/language candidates, and `unresolved` flag. Output text is NFC-normalized
only if normalization does not destroy visible distinctions; original visible
lexeme remains available. No translation occurs. Ambiguous glyphs render as
`⟦unclear:<candidate-or-?>⟧` with a receipt warning and source bounds.

Highlights and handwritten annotations are separate typed regions linked by
`attached_to_region_ids`; they are never merged destructively into cell text.
Markdown adds a readable note immediately after the affected text/table.

### Tables and forms

Logical cells are keyed by row/column and carry row span, column span, missing
state, text spans, annotations, bounds, and confidence. A missing cell differs
from an observed empty cell. Markdown uses a conventional table only when the
topology is rectangular without destructive span loss; otherwise it renders a
readable indexed-cell table and includes span metadata in the structured block.
Forms render field label/value/status tables in reading order.

### Charts

Panel IDs are stable within the source hash. Axes record labels,
linear/log/category scale, visible min/max ranges, and ordered tick lexemes and
values. Series carry units and bind to explicit panel and legend identities.
Legend entries map visible labels/markers to series, while annotations identify
their target series and point index. `ChartPointV1` has:

```text
index, x_lexeme, x_value?, y_lexeme, y_value?, status,
uncertainty_low?, uncertainty_high?, source_bounds?, calibration_method?
```

`observed` requires a visible numeric lexeme. `calibrated` requires a stated
axis calibration method and uncertainty bounds. `missing` has no invented
value. `ambiguous` preserves candidates/lexeme and uncertainty. Increased
sampling density does not imply increased certainty. Multi-chart output preserves panels,
shared legends, and shared axes.

## Profile format and selection

Caret config owns named `[image_read_profiles]`. Each `ModelProfileV1` resolves:

- provider and model/revision;
- endpoint and secret reference;
- `location: local|remote` and `egress: deny|allow`;
- declared vision capability and supported MIME/detail modes;
- detail, maximum tokens, request/response/image bytes and pixels;
- timeout (default 30 s, ceiling 120 s), concurrency and queue depth;
- full-image/crop/retry limits; and `fallback: none`.

The default image profile is local. `image-to-markdown --profile <id>` and the
SPipe `image_read_profile` setting select by ID. Missing ID, undeclared vision,
or forbidden egress fails before image payload transmission. Secrets are
resolved by the existing Caret config facade after admission.

## Parsing and provider serialization

The proxy parser accepts OpenAI-compatible message arrays containing string
content or ordered typed content arrays. It validates role and parts before
dispatch and retains all system/user/assistant ordering. Provider serializers
escape JSON centrally and map `ImageDetailV1` explicitly. They must not pass a
local path to a remote provider; remote payloads use already-admitted bounded
bytes/data URLs. Local compatible providers receive only supported source form.

Serializer unit tests use fixed images and assert payload structure without
logging base64. Existing text-only payload golden tests stay unchanged.

The provider transport selects certificate-verifying H1/TLS for `https://`
and native HTTP v2 only for admitted loopback `http://`. HTTPS calls use one
absolute deadline and do not follow redirects; provider response bodies are
bounded to 8 MiB before JSON parsing.

## Orchestrator algorithm

`extract_image_to_markdown_v1(input, policy, client, cache, publisher)`:

The selected NFR permits one request containing the complete image plus at
most four uncertain-region crop retries. The three protocol stages are explicit
nested snapshots in one `image-three-stage-pipeline.v1` response envelope, not
three complete-image uploads. Crop refinement remains optional gated work.

1. Canonicalize and authorize input under allowed roots.
2. Read once with byte bound; hash, decode, orient, and validate dimensions.
3. Compute complete cache key and return verified scoped hit if present.
4. Send one admitted full-image request using `three_stage_pipeline_prompt_v1`.
5. Parse the versioned envelope and independently validate its inventory,
   extraction, and audit documents. Before JSON parsing, reject response text
   larger than `max_output_tokens * 16` bytes; provider transport also retains
   its independent 8 MiB absolute response ceiling.
6. Require ordered region, table, and chart identities in extraction/audit to
   equal the structural inventory; fully validate the audited document.
7. If a future crop-refinement lane is enabled, rank optional unreadable regions
   deterministically and use at most four bounded crops; the current path emits
   them explicitly in `unresolved` and performs no additional model request.
8. Run final cross-stage validation and structured reliability diagnostics.
9. Render Markdown and canonical JSON from the same immutable document.
10. Store the validated structured result in the trust-scoped cache, then build
    the receipt and atomically publish the Markdown, JSON, and receipt. Cache
    write failure is terminal; receipt-last hash admission prevents a partial
    set from being accepted as a valid generation.

Any terminal error proceeds to a failure receipt publication when safe. No
partial document is returned as success. Retry eligibility is a typed matrix,
not substring matching.

“Unresolved required field” means a missing or invalid structural field needed
to decode or validate the schema (identity, bounds, topology, category, chart
association, or provenance); it is terminal. The `unresolved` array represents
optional visible content that cannot be read faithfully and may remain in a
successful document when explicitly identified. A future typed unresolved-item
contract may replace these strings without weakening this distinction.

## Prompt protocol

The prompt ID is `image-three-stage-pipeline-v1`. It declares the exact
versioned envelope schema, source-as-untrusted rule, no-tool/no-URL/no-
translation policy, category vocabulary, ambiguity representation, and
observed-versus-calibrated distinction for all three snapshots.

Inventory cannot emit final values. Extract cannot omit inventory regions
without an explicit reason. Audit checks but cannot invent missing evidence.
The canonical prompt version and extraction schema version are imported from
`prompts.spl`, included in the structured-result cache key, and recorded in the
receipt. Schema v2 invalidates v1 cached extraction documents. Cache hits are
decoded, validated, and rendered with the current renderer before publication.

## Markdown layout

The current renderer emits these stable sections:

```text
# Image dataset
## Source and provenance
## Page inventory
### Regions
## Text and handwriting
## Tables and forms
## Charts and graphs
```json
{ canonical chart subset }
```
## Additional region content
## Unresolved items
## Warnings
```

The region manifest preserves ID, canonical category, reading order,
confidence, page, and source bounds. Typed table/text/chart bodies render in
their dedicated sections; chart subtype region prose is not repeated. Other
categories retain their Markdown under `Additional region content`. Every
chart tick, legend, annotation, and numeric sample source box uses
`[page_index,x,y,width,height]`. JSON keys and arrays have deterministic order.
Markdown is understandable without opening JSON; all calibrated, missing, and
ambiguous values are called out in prose.

Chart regions and `chart_type` values use closed snake-case vocabularies. The
typed chart families include line, bar, scatter, area, pie/donut, histogram,
box/violin, heatmap/contour, cell distribution, scientific, radar, bubble,
candlestick, waterfall, treemap, sunburst, funnel, polar, choropleth, density,
and error-bar; unrecognized evidence is `unknown`, never an invented label.

## Receipt and artifacts

`ExtractionReceiptV1` records source/result/artifact hashes,
dimensions, provider/model/revision, profile fingerprint,
prompt/extraction-schema/preprocessing/renderer versions, status, a distinct safe
error code, warnings, retry/request counts, cache-hit state, provenance-item and
validation-check/failure counts, and per-phase
timing slots. Until the provider boundary exposes trusted split timing, the
orchestrator records its measurable call-plus-envelope-validation interval as
an upper bound in `transport_ms`, sets `inference_ms` to zero, and emits an
explicit warning rather than fabricating a split. NFR-009 remains open for exact
transport timing. Receipt schema v3 makes the observability
fields machine-readable without exposing provider response content or credentials.

Each document JSON, Markdown, and receipt file uses atomic replacement. The set
is admitted receipt-last: consumers must ignore Markdown/JSON until the receipt
exists and its hashes match both files. Best-effort rollback reduces debris but
is not the consistency boundary; a restoration failure leaves no valid new
receipt and therefore cannot admit the partial generation.
The evidence sidecar references immutable paths/hashes and uses pixel-region
selectors where applicable. The structured cache is independent of artifact
publication and is written after document validation, before artifact writes.

## SPipe action

Public action name: `image_to_markdown`. Required inputs are `image_path`,
`artifact_root`, `allowed_roots`, and explicitly selected
`image_read_profile`. Optional settings may narrow limits but cannot exceed the
profile ceiling.

Action outcomes are `completed`, `skipped`, and `failed`; a cache hit is a
`completed` action whose receipt warning contains `cache hit`. `skipped`
performs no model call. On completed results, bindings expose
`markdown_path`, `document_path`, `receipt_path`, and their hashes. Evidence is
typed `artifact`/`api` evidence. Expected assertions must come from independent
fixture references.

## Codex image-read skill

Create `.codex/skills/image-read/SKILL.md` with automatic discovery metadata.
The skill must:

1. locate an explicitly configured image profile;
2. refuse remote egress unless that profile permits it;
3. invoke the compiled `image-to-markdown` surface;
4. report Markdown/document/receipt paths and typed failures;
5. never reproduce secrets, image data URLs, or entire extracted datasets in
   chat when artifacts are available;
6. preserve uncertainty and never describe calibrated arrays as exact.

Parallel Claude/Gemini skill mirrors, if later requested, must call the same
application rather than copy extraction logic.

## Validation and error handling

Validation is layered: request policy, decoded image, inventory schema,
document schema, reference integrity, semantic consistency, audit consistency,
artifact hash. Unknown fields may be retained only in an extension map; missing
required fields fail. Unknown category values map to `unknown` plus warning,
not an invented known category.

Errors use `Result<T, MultimodalErrorV1>` and `?`. Safe diagnostics include
stage, code, request ID, hashes, dimensions, counts, and provider status class.
They exclude raw bytes, base64/data URLs, secrets, and unrestricted model text.

## Cache details

The current cache-key function serializes canonical fields before hashing. It
includes source hash, the trust-scoped profile fingerprint (which covers
provider/model/revision and configured limits), prompt/schema/preprocessing
versions, and image detail. It stores validated structured JSON rather than
published artifacts, so cache hits verify the cache content digest and are
decoded, validated, and rendered again. Renderer version is intentionally not
part of this key. Corrupt or missing entries are not served.

## Concurrency and resources

A bounded queue admits extraction runs; concurrency is profile-limited. Each
run owns its decoded image and immutable stage results. Region retries can be
parallel only within remaining profile concurrency and are committed in stable
region order. Cancellation stops new requests, releases buffers, and writes a
cancelled failure receipt when possible.

## Performance verification

Use a checked-in realistic redacted fixture after one warm-up. Measure 20 warm
runs for local preprocessing/proxy overhead, excluding model/network time,
reporting p50/p95 and max RSS. Gate warm p95 below 100 ms. Also verify one
source read/decode, zero model-discovery subprocesses, bounded retries (<=4),
bounded queue, and no full-tree scan on the request path.

## System-test manual contract

Executable scenario path is planned as
`test/03_system/app/image_to_markdown/feature/image_to_markdown_multimodal_pipeline_spec.spl`;
its manual mirrors to
`doc/06_spec/03_system/app/image_to_markdown/feature/image_to_markdown_multimodal_pipeline_spec.md`.

Frozen visible step text:

- `step("Configure an explicit local vision profile")`
- `step("Extract a highlighted multilingual table image")`
- `step("Extract a single-chart image into numeric arrays")`
- `step("Extract a multi-panel chart without losing panel identity")`
- `step("Publish Markdown, structured data, and a synchronized receipt")`
- `step("Reject unsafe, unsupported, or unconfigured image requests")`

Frozen setup helpers:

- `given_private_fixture_workspace()`
- `given_local_image_read_profile()`
- `given_deterministic_vision_fixture_provider()`
- `given_clean_image_artifact_root()`

Frozen action/checker helpers:

- `when_image_to_markdown_runs(fixture_name)`
- `check_ordered_multimodal_parts_preserved()`
- `check_markdown_matches_reference(fixture_name)`
- `check_table_topology_and_annotations()`
- `check_original_scripts_preserved()`
- `check_graph_samples_and_uncertainty()`
- `check_multi_panel_identity()`
- `check_receipt_artifact_hashes()`
- `check_no_model_call_occurred()`
- `check_safe_typed_failure(code)`

Until implemented, every helper body must call
`fail("NOT IMPLEMENTED: <exact-helper-name>")` (or `assert(false)` where `fail`
is unavailable). No `pass_todo`, empty body, canned success, or
`expect(true).to_equal(true)` is permitted. Scenario-generated manuals hide
setup with `@inline`/`@prev`, show primary steps, fold detailed matrices, and
link `text`, `api`, and `artifact` evidence captures.

## Requirement coverage design

- REQ-001/002/007 and NFR-007: contract, role/part order, Unicode, and legacy
  proxy integration tests.
- REQ-003/011/015 and NFR-001/003/008: profile, capability, egress, timeout,
  missing configuration, and typed-failure scenarios.
- REQ-004/005: three-stage protocol and category corpus scenarios.
- REQ-006: independent table topology/form/highlight references.
- REQ-008/009: single/multi-chart axis, label, sample, lexeme, calibration, and
  uncertainty references.
- REQ-010/012: deterministic rendering, stable paths, hashes, and sidecar tests.
- REQ-013: skill discovery and compiled-surface contract test.
- REQ-014: full-key, trust-isolation, invalidation, corruption, and eviction
  tests.
- NFR-002/004/009/012: limit, performance, timing/counter, one-read, and
  no-scan/no-subprocess gates.
- NFR-005/010: acceptance-corpus parse-rate report and private-real-image recipe.
- NFR-006/011: receipt completeness and Markdown readability review.
