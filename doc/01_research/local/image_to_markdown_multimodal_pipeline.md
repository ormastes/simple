<!-- codex-research -->
# Image-to-Markdown Multimodal Pipeline — Local Research

## Scope

The requested feature turns document images into a complete Markdown dataset. It must distinguish at least: tables/forms with highlights, multilingual handwriting, one graph, multiple graphs, and additional document categories; graphs must include high-definition numeric series rather than prose alone. The same capability must be callable from LLM Caret/Codex/Claude through the Slang LLM proxy and from SPipe when a vision model is configured.

## Existing owners

- `src/app/llm_caret/provider.spl` already centralizes provider dispatch for Claude/Codex CLIs, hosted OpenAI/Anthropic-compatible APIs, Slang, Slang-local, and local Torch. Its request contract is text-only (`prompt`/`messages_json`).
- `src/app/llm_caret/main.spl` (`proxy_handle`, `proxy_handle_stream`, `_proxy_dispatch`) currently reduces inbound requests to one content string and reconstructs one user message. This loses roles and image parts before provider dispatch.
- `src/app/llm_caret/types.spl` defines a text-only `Message`, so the fix must preserve normalized content parts at this established proxy boundary rather than creating a parallel proxy.
- `src/app/llm_caret/openai_api.spl` and `src/lib/nogc_async_mut/llm/openai_api.spl` build Chat Completions requests. Messages currently serialize `content` as a JSON string, so they cannot express typed image parts.
- `src/lib/nogc_async_mut/llm/openai_compat.spl` is the natural wire adapter for Ollama, LM Studio, vLLM, LocalAI, and Slang's OpenAI-compatible server, but it has the same text-only message limitation.
- `src/app/llm_caret/config.spl` is the existing provider/model/base URL/key configuration owner. Secret lookup must stay behind its environment/config facade rather than new leaf-level environment reads.
- `src/app/spipe/` owns SPipe orchestration and evidence metadata; `src/app/spipe_docgen/` renders executable scenarios into Markdown manuals. Image analysis should be an explicit task/evidence kind, not an implicit docgen side effect.
- `src/app/spec_to_sspec/spipe_evidence_emit.spl` and `src/app/spec_to_spipe/` are adjacent evidence-contract work and should be reused for artifact provenance rather than inventing a second receipt format.
- `src/lib/common/spec/evidence/model.spl`, `src/lib/common/spec/evidence/format/evidence_sidecar.spl`, and `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl` are the concrete reusable evidence model, sidecar, and loader owners.
- `src/lib/common/imaging/png_ingest.spl`, `src/lib/common/image/`, and `src/lib/nogc_sync_mut/io/image_sffi.spl` provide image ingestion/metadata primitives, but no OCR or document-layout abstraction.
- Existing chart-domain research at `doc/01_research/hardware/nand_analysis/nand_distribution_gss_asmd_chart_digitization.md` shows a concrete need for extracting plotted numeric distributions.

## Gaps

1. No provider-neutral image input, MIME/source descriptor, region/crop, image-detail policy, or multimodal capability negotiation exists.
2. No canonical structured result exists for Markdown, tables, text spans, highlights, handwriting/language, chart panels, axes, series, uncertainty, and provenance.
3. No three-stage prompt/validation contract exists. Free-form Markdown alone cannot prove graph arrays are numeric, aligned to axes, or complete.
4. No SPipe model-selection hook invokes vision only when configured, and no deterministic fixture adapter permits offline system tests.
5. No image-reading Codex skill routes an operator through classification, extraction, validation, and artifact publication.

## Recommended ownership boundary

Use provider-neutral `ContentPartV1`, `MultimodalRequestV1`, and `ModelProfileV1` contracts; keep provider JSON in provider adapters; make LLM Caret the policy/configuration facade; orchestrate extraction in `src/app/image_to_markdown/`; and add an SPipe image-analysis action that persists Markdown plus the existing machine-checkable evidence sidecar. `ExtractionDocumentV1` should be the canonical structured observation and `ExtractionReceiptV1` should bind hashes, model/profile, schema/prompt/preprocessing versions, timings, and status. Extracted content is evidence, never its own expected test oracle. Do not put image decoding, full-tree scans, or per-region subprocess discovery in request handlers.

## Astra architecture review

The highest-capability review recommends preserving decimal lexemes, leading zeros, exponents, missing cells, ambiguous digits, source boxes, and panel/axis/legend identity. Approximate curve digitization must carry calibration and uncertainty and must never be labeled as exact observation. Local endpoints should be the safe default; remote egress and fallback must be explicit. Cache keys must include the source hash and complete extraction configuration and be isolated by trust scope.

## Knowledge-route receipt

The current registry has no exact feature route. The provisional feature is `image_to_markdown_multimodal_pipeline`; the closest feature group is app/tooling and the longest relevant source prefixes are `src/app/llm_caret`, `src/app/spipe`, and `src/lib/nogc_async_mut/llm`. This ambiguity is recorded in `.spipe/image_to_markdown_multimodal_pipeline/knowledge_selection.sdn` without editing the registry, which is currently dirty in another session.

## Concurrent-work note

The worktree contains extensive unrelated active edits, including the knowledge registry, compiler/core, MCP, and SPipe graph/docgen files. Those changes are treated as other-session work and must not be folded into this feature.
