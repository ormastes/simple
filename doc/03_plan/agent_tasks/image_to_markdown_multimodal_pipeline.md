<!-- codex-design -->
# Agent Tasks: Image-to-Markdown Multimodal Pipeline

## Coordination contract

The architecture and detail design freeze the shared contract names, step text,
helper names, error policy, and fail-fast placeholder policy before sidecars
start. All agents preserve unrelated dirty work. Merge owner is **root**. Final
reviewer is **Astra (highest-capability architecture/quality review)**.

No lane may create executable specs under `doc/06_spec`, flatten images into
prompt paths, add implicit provider fallback, or make observed model output its
own oracle.

## Shared-name baseline

Implemented interface names are frozen only where they exist. Names in this
baseline that are not present in source remain proposed and must not be cited
as completed interfaces:

`ContentPartV1`, `ImagePartV1`, `ImageCropV1`, `MultimodalMessageV1`,
`MultimodalRequestV1`, `VisionCapabilitiesV1`, `ModelProfileV1`,
`ModelCompletionV1`, `MultimodalErrorV1`, `MultimodalClientV1`,
`ExtractionPolicyV1`, `ExtractionDocumentV1`, `ExtractionPageV1`,
`ExtractionRegionV1`, `SourceBoundsV1`, `TextSpanV1`, `TableV1`,
`TableCellV1`, `AnnotationV1`, `ChartV1`, `ChartPanelV1`, `ChartAxisV1`,
`ChartSeriesV1`, `NumericSampleV1`, `ExtractionReceiptV1`,
`ExtractionArtifactsV1`, `ArtifactPublisherV1`, and `ExtractionCacheV1`.

Prompt ID: `image-three-stage-pipeline-v1`; one full-image request returns the
inventory, extraction, and audit snapshots in a versioned envelope.
SPipe action: `image_to_markdown`. Codex skill: `image-read`.

Manual step strings and helper/checker names are exactly those in
`doc/05_design/image_to_markdown_multimodal_pipeline.md`; changes require merge
owner approval before any lane proceeds.

Placeholder rule: use `fail("NOT IMPLEMENTED: <exact-helper-name>")`, or
`assert(false)` only when `fail` is unavailable. Never use `pass_todo`, empty
bodies, canned successful artifacts, or tautological assertions.

## Lane 0 — merge owner and interface gate

Owner: root. Sidecar: N/A. Dependencies: none.

- Confirm approved requirements and knowledge receipt.
- Land shared contracts and compile-only compatibility scaffolding first.
- Publish exact module/file ownership to lanes; resolve overlap before edits.
- Keep a requirement-to-test matrix and integrate in dependency order.
- Run no check more than once after it passes in this session.

Exit: shared types compile, text-only constructors remain compatible, and all
downstream lanes target the frozen interfaces.

## Lane 1 — Caret multimodal boundary and providers

Primary owner: implementation agent assigned by root.
Lower-model sidecar: Codex Spark for provider-payload inventory only; it may
report adapter differences but must not accept generated payload quality.
Files: `src/app/llm_caret/**`, targeted
`src/lib/nogc_async_mut/llm/openai_compat.spl`, corresponding unit/integration
tests only.

- Implement multimodal values, validation, request parsing, role/part retention,
  capability admission, and text compatibility.
- Extend OpenAI/Slang-compatible and supported provider serializers.
- Add profile resolution through existing config/environment owners.
- Prove unsupported vision and unsafe egress fail before transport.

Exit: ordered multimodal transport tests pass; legacy text-only proxy tests pass;
no image bytes/data URLs/secrets appear in logs.

## Lane 2 — extraction core and deterministic renderer

Primary owner: implementation agent assigned by root.
Lower-model sidecar: Claude Haiku for fixture taxonomy/reference inventory only.
Final fixture exclusions and fidelity decisions require Astra review.
Files: new `src/app/image_to_markdown/**`, unit tests, checked-in synthetic or
redacted fixture/reference data.

- Implement bounded ingest, three-stage prompts/orchestration, validation,
  uncertainty-aware graph data, tables/forms/handwriting/annotations, renderer,
  receipt, atomic publication, and scoped cache.
- Use injected deterministic provider for offline tests.
- Preserve English/Korean/Japanese/Simplified and Traditional Chinese and
  ambiguous glyph markers without translation.

Exit: independent references verify category, topology, scripts, panels,
numeric status/uncertainty, deterministic Markdown/JSON, and receipt hashes.

## Lane 3 — SPipe action, evidence, system spec, and skill

Primary owner: implementation agent assigned by root.
Lower-model sidecar: Claude Sonnet for generated-manual readability draft
review; root/Astra must accept all edits and done marks.
Files: targeted `src/app/spipe/**`, existing evidence extension points,
`test/03_system/app/image_to_markdown/feature/**`, mirrored Markdown manual,
test plan, and `.codex/skills/image-read/**`.

- Add explicit-profile SPipe action and stable artifact bindings.
- Reuse evidence sidecar/pixel selectors; do not add inference to docgen.
- Implement frozen manual steps/helpers with real independent assertions.
- Generate the manual and iterate once for readability/stub count.
- Add discoverable skill invoking the compiled application surface.

Exit: absent profile causes no model call; success publishes all three hashed
artifacts; generated manual explains primary flows and reports zero stubs.

## Lane 4 — security, limits, and performance evidence

Primary owner: verification agent assigned by root.
Lower-model sidecar: Codex Spark for static hot-path scan candidates only.
Broad exclusions, benchmark validity, and PASS/FAIL belong to Astra.
Files: targeted security/performance tests and evidence reports; production
code changes return to owning lane.

- Test root/symlink escape, malformed/oversized images, prompt injection,
  forbidden egress, secret/log redaction, timeouts, response truncation, queue
  and concurrency bounds.
- Measure warm local overhead p50/p95 and max RSS on declared fixture, excluding
  inference/network; gate p95 below 100 ms.
- Prove one source read/decode, <=4 uncertain-region retries, zero hot-path
  model-discovery subprocesses, and no full-tree scans.
- Run acceptance-corpus structured parse-rate evaluation and require >=95%.

Exit: NFR evidence is reproducible and limitations are explicit.

## Integration order

1. Lane 0 shared contracts and compatibility gate.
2. Lane 1 neutral client/provider path and Lane 2 pure extraction model can
   proceed in parallel after the gate.
3. Root integrates Lane 1 and Lane 2, then demonstrates one deterministic
   end-to-end extraction.
4. Lane 3 binds the stable service into SPipe/evidence and generates the manual.
5. Lane 4 runs security/performance/acceptance evidence; fixes return to owners.
6. Root runs required compiler/lib/MCP/LSP and environment-facade checks because
   the work touches `src/lib` and tool-server behavior.
7. Astra performs final requirement, architecture, generated-manual, security,
   and performance review and emits PASS/FAIL/WARN. Release remains separate.

## Merge and ownership safeguards

- Each lane checks worktree status immediately before editing and reports
  pre-existing dirty files. Do not stage or commit unrelated paths.
- `src/app/llm_caret/config.spl`, `provider.spl`, `main.spl`, SPipe evidence
  owners, and shared LLM adapter files are single-writer during integration.
- Root resolves contract changes; sidecars do not rename frozen interfaces.
- Tests use only canonical matchers: `to_equal`, `to_be`, `to_be_nil`,
  `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, and
  `to_be_less_than`.
- Verification observes the three-cycle cap and never reruns an already-green
  acceptance check in the same session.

## Final review checklist

- REQ-001..REQ-015 and NFR-001..NFR-012 have independent evidence.
- Existing text-only Caret behavior is unchanged.
- Local profile is default; remote egress and profile selection are explicit.
- All source/model/prompt/schema/preprocessing settings participate in cache
  identity and cache entries are trust isolated.
- Markdown is readable alone; chart arrays retain lexemes, status, bounds, and
  uncertainty; multi-panel identity is intact.
- SPipe performs no call when the image profile is absent and never uses output
  as its own oracle.
- Skill is discoverable and reports artifact paths without leaking source data.
- No raw image/data URL/secret logging, full-tree hot scan, repeated source read,
  or per-request discovery subprocess exists.
- Generated manual has zero stubs and no `.spl` exists under `doc/06_spec`.
- Direct environment/runtime guard and all scope-required checks pass once.
