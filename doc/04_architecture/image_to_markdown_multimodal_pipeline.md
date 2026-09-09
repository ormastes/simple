<!-- codex-design -->
# Image-to-Markdown Multimodal Pipeline Architecture

## Status and decision

Status: approved design baseline, 2026-09-08. The selected requirements are
`A + D1 + G1 + F1 + L1 + N1 + C1`.

The system adds typed multimodal messages at the existing LLM Caret boundary,
keeps provider wire formats inside adapters, and gives the new
`image_to_markdown` application sole ownership of document extraction. SPipe
invokes that application only through an explicit image-read profile and
publishes its outputs through the existing evidence sidecar model.

This is an adapter-and-orchestrator design, not a second LLM proxy and not a
compiler MDSOC transform. Runtime composition is needed at provider and
artifact-store boundaries; compile-time weaving would obscure security and
ownership. The feature therefore uses explicit traits and value contracts.

## Architectural invariants

1. Ordered roles and ordered content parts survive proxy parsing unchanged.
2. Provider adapters alone know OpenAI, Anthropic, CLI, or Slang wire JSON.
3. Image bytes never enter logs, diagnostics, cache keys, or receipts.
4. A remote call occurs only when the selected profile explicitly allows it.
5. No configured vision capability means a typed failure, never fallback.
6. Markdown and the structured document are deterministic projections of the
   same validated extraction object.
7. Model output is observation evidence and never its own expected oracle.
8. Approximate chart values are labelled calibrated and carry uncertainty.
9. Hot requests do no full-tree scans, model-discovery subprocesses, or source
   rereads after ingestion.
10. Existing text-only constructors and routes retain their behavior.

## Layer and ownership map

```text
SPipe action / Caret HTTP client / CLI
                  |
                  v
src/app/image_to_markdown/             extraction application owner
  profile -> ingest -> one-call three-stage envelope -> validate -> render
                  |
          MultimodalClientV1 trait
                  v
src/app/llm_caret/                      policy and provider selection owner
  multimodal contracts + profile resolution + capability admission
                  |
                  v
src/app/llm_caret/*_api.spl and
src/lib/nogc_async_mut/llm/openai_compat.spl
                                        provider wire adapters

src/lib/common/image/                   decoded image primitives only
src/lib/common/spec/evidence/           canonical evidence/sidecar owner
src/app/spipe/                           orchestration and artifact binding
```

Dependencies point downward in the diagram. Provider adapters may import the
neutral contracts but cannot import the extraction application. SPipe knows an
image-analysis action and artifact descriptors, not provider JSON. Image
libraries do not read environment or select models.

## Module allocation

### Shared multimodal contracts

Create `src/app/llm_caret/multimodal_types.spl` as the canonical application
boundary. It owns the following versioned values:

- `ContentPartV1`: a closed `text`/`image` value. Text carries only content;
  images carry a host-admitted artifact ID, MIME, hash, detail, decoded
  dimensions, and a transient data URL that is never logged or receipted.
- `MultimodalMessageV1`: validated role and ordered parts.
- `MultimodalRequestV1`: ordered messages plus the immutable selected profile
  and prompt/schema/preprocessing versions.
- `VisionCapabilitiesV1`: accepts images, supported MIME/detail/source kinds,
  maximum images/bytes/pixels, structured-output support.
- `ModelProfileV1`: provider, model, optional revision, endpoint, secret
  reference, local/remote classification, vision declaration, detail, limits,
  concurrency, egress, retry, and fallback policy.

Compatibility constructors map the old `Message(role, content)` to one text
part. No old caller is required to manufacture multimodal values.

`src/app/llm_caret/multimodal_types.spl` owns role, one-of, MIME, bounds,
limits, endpoint/egress, extraction topology, and capability checks. `src/app/llm_caret/config.spl`
remains the only profile/secret/environment owner; leaf modules receive an
already resolved profile and redacted secret handle.

### Caret proxy and adapters

`src/app/llm_caret/main.spl` preserves the structurally parsed ordered message
array without collapsing it to `_last_user_content`. OpenAI and Anthropic wire
parts are converted at the provider boundary, including Anthropic top-level
system text. Text-only requests continue through the legacy route.

`multimodal_provider.spl` admits typed requests only after profile, content,
byte, pixel, count, endpoint, egress, and capability validation. Its
`complete_multimodal_v1` entry returns `ModelCompletionV1` with typed timeout,
truncation, unsupported-provider, and transport errors.

Hosted HTTPS uses the existing certificate-verifying browser H1/TLS stack with
an aggregate DNS/connect/handshake/write/read deadline. It is single-hop so an
authorization header cannot cross origins through redirects. Explicit
loopback HTTP profiles use HTTP v2. Both routes reject responses above 8 MiB.

OpenAI/Slang-compatible adapters render typed content arrays in
`openai_api.spl` and `openai_compat.spl`. Anthropic and CLI adapters translate
the same neutral values. A CLI route that cannot securely provide image parts
reports `provider_vision_unsupported`; it does not flatten file paths into a
prompt. Provider response JSON remains below the adapter boundary.

### Extraction application

`src/app/image_to_markdown/` has these concrete owners:

- `input.spl`: permitted-root validation, bounded PNG read, decoded dimensions,
  source hash, and data-URL materialization.
- `prompts.spl`: immutable prompt/schema versions and the one-call three-stage
  envelope instruction.
- `service.spl`: the bounded envelope decoder and cross-stage validator.
- `extraction_json.spl`: strict wire-to-`ExtractionDocumentV1` decoding and
  validation before rendering or publication.
- `markdown.spl`: deterministic Markdown projection.
- `artifacts.spl`: receipt-last Markdown/JSON publication, rollback, and admission.
- `cache.spl`: trust-scoped, digest-verified result reuse.
- `app_service.spl` and `main.spl`: configured orchestration and direct CLI.

Provider-neutral contracts live in `src/app/llm_caret/multimodal_types.spl`;
configured profiles and provider serialization live beside them in
`image_profile.spl`, `image_completion.spl`, and `multimodal_provider.spl`.
- `service.spl`: CLI/service entry facade; returns artifact descriptors.

Local admission identifies PNG, JPEG, and WebP from bytes rather than file
extensions. PNG uses the full decoder; JPEG scans bounded marker segments to a
SOF frame; WebP validates RIFF size and VP8/VP8L/VP8X dimension headers.

The orchestrator depends on the `MultimodalClientV1` interface, injected by
Caret in production and by a deterministic fixture adapter in tests. It never
spawns a provider process itself.

### SPipe integration

Add an explicit `image_to_markdown` action under `src/app/spipe/`. Its config
requires `image_read_profile`; absence yields a skipped/not-configured typed
result without invoking a model. The action receives an allowed input root and
stable run artifact root, invokes the service, and publishes:

```text
<output-dir>/<validated-base-name>.md
<output-dir>/<validated-base-name>.json
<output-dir>/<validated-base-name>.receipt.json
```

The SPipe adapter records those paths and SHA-256 values through
`src/lib/common/spec/evidence/model.spl` and
`src/lib/common/spec/evidence/format/evidence_sidecar.spl`. It must not modify
SPipe docgen to perform inference. Docgen may render links to already-produced
artifacts.

## Canonical extraction model

`ExtractionDocumentV1` contains source metadata, page list, ordered regions,
global warnings, and audit status. A region has stable ID, category, reading
order, pixel bounds, detected scripts/languages, confidence, provenance, and a
typed payload. Categories are composable: printed text, table, form,
highlight/annotation, handwriting, signature/stamp, single or multiple charts
(histogram, line, bar, scatter, area, pie, box/violin, heatmap, contour),
scientific plots, flowcharts, networks, schematics, timelines/Gantt, diagrams,
equations, chemical structures, musical notation, code, maps, photos,
screenshots, barcode/QR, mixed pages, and unknown.

Tables retain rows, columns, logical cells, row/column spans, missing state,
visible lexeme, normalized value only when justified, bounds, confidence, and
attached annotation IDs. Handwriting preserves Unicode source text without
translation; unresolved glyphs use an explicit marker and source box.

Charts contain panel IDs; chart subtype; axes with scale/range/unit; legends;
series; and ordered `NumericSampleV1` values. A numeric sample contains source
lexeme, optional parsed value, status (`observed`, `calibrated`, `missing`, or
`ambiguous`), uncertainty interval/error, source box, panel/axis/series IDs,
and calibration method. Arrays preserve point order and visible precision.

## Three-stage execution

One provider request sends the admitted full image and asks for a versioned
envelope containing three ordered snapshots: **inventory** (structure only),
**extraction** (canonical content), and **audit** (checked final content). The
service strictly decodes every snapshot, rejects inventory content leakage,
requires structural and source identity across stages, and publishes only the
audited document. Optional future crop refinement may use at most four requests;
the current implementation makes none. A failed envelope writes a receipt with
a typed safe error code and bounded diagnostic, never the raw response.

## Startup and hot paths

### Startup

Caret loads configuration once, resolves profiles and secret references, and
builds an immutable provider-capability index. Image-to-Markdown registers its
prompt/schema versions and cache namespace. SPipe registers the action. Startup
does not probe every installed model or launch a CLI. Optional explicit
`profile check` is a maintenance operation outside startup.

### Hot request path

The hot path is: resolve indexed profile -> enforce policy -> ingest once ->
hash/decode once -> cache lookup -> one full-image call carrying three explicit stage snapshots -> validate ->
render once -> publish files with receipt-last hash admission. Crops derive from the retained
decoded image. Provider adapters reuse configured HTTP/session infrastructure.
No full-tree scan, repeated model discovery, request-time compiler invocation,
or per-stage source reread is allowed.

### Cache and invalidation

The structured-result cache key is a hash over source hash, provider/model/revision,
the trust-scoped profile fingerprint excluding secret value, prompt version,
schema version, preprocessing version, and image detail. Schema v2 is the first
version containing explicit axis ranges/ticks, legend mappings, and annotation
targets, so v1 entries naturally miss. Cached structured results are validated
and rendered again; renderer changes therefore do not require model re-extraction.
Entries are never shared across trust scopes. Failed/truncated outputs are not
success entries. Bounded LRU/size policy and explicit administrative purge are
the only mutation mechanisms; publication uses write-then-rename.

## Security and privacy

- Local is the default profile; remote egress must be explicit in that profile.
- Allowed filesystem roots are passed by the caller and checked before open and
  after canonicalization. Symlink escape is rejected.
- Remote image URLs are disabled for extraction by default; document content
  cannot cause URL fetches, tools, file reads, or profile changes.
- Secret references are resolved only by Caret config through the repository
  environment facade. Receipts contain reference names/fingerprints, never
  secret values.
- Diagnostics contain request ID, stage, typed code, sizes, and hashes, never
  raw image bytes/data URLs. Provider responses are size bounded.
- Prompt text labels all image/document content as untrusted evidence and
  forbids following instructions found within it.
- Limits apply before allocation where possible: 20 MiB decoded input by
  default, bounded pixels/tiles/images/queue/tokens/request/response/concurrency.

## Performance and observability

Warm p95 load/decode, preprocessing, validation, rendering, and proxy overhead
combined (excluding inference/network) must be below 100 ms on the repository
benchmark fixture. Default timeout is 30 s, configurable to at most 120 s. One
full-image request plus at most four uncertain-region retries is the default.

The required observability target is bounded timings for cache lookup,
load/decode, preprocessing, transport, inference, validation, rendering, and
publication, plus counters for requests, cache hits/misses, retries, validation
failures, limit failures, and provider failures. The current receipt exposes
timing slots but combines provider transport and inference; split timing and
the broader counters remain gated implementation work. Debug output may report
only hashes, dimensions, counts, profile fingerprint, and timings. Performance
tests must report warm p50/p95, max RSS, fixture dimensions/bytes, and
model/network exclusion boundaries.

## Error model

`MultimodalErrorV1` is a closed typed code plus safe message and stage. Codes
include malformed image, unsupported MIME/provider/model capability, model
unavailable, profile absent, unsafe root/egress, size/pixel/concurrency limit,
timeout, truncated response, invalid structured output, unresolved required
field, cache corruption, and publication failure. Errors are terminal unless
the profile explicitly permits a bounded retry for that code. Provider fallback
is always `none` in the approved policy.

## Testing and traceability boundary

Transport contract tests assert role/part order and provider payloads. Offline
fixture-provider system tests assert the single-call three-stage envelope and deterministic
artifacts. Independent checked-in synthetic/redacted reference data measures
OCR, script preservation, table topology, highlight attachment, chart labels,
numeric tolerance, uncertainty, and panel completeness. No assertion derives
its expected value from the model response being tested.

Every REQ-001..REQ-015 and NFR-001..NFR-012 must map to at least one system,
integration, unit, security, or performance check. Placeholder scenarios must
fail with `assert(false)` or `fail("NOT IMPLEMENTED: <helper>")`; `pass_todo`,
empty bodies, and tautological expectations are forbidden.

## Rejected alternatives

- **Parallel proxy:** duplicates auth, provider policy, and config and would
  leave existing role/image loss unfixed.
- **Markdown-only model response:** cannot validate table topology, provenance,
  chart precision, or synchronized receipts.
- **Docgen-triggered inference:** makes documentation nondeterministic and turns
  observed output into an accidental oracle.
- **Implicit remote/provider fallback:** violates privacy, reproducibility, and
  the selected failure policy.
- **Prompt-carried file paths:** invites unintended file access and does not
  provide typed image transport.
