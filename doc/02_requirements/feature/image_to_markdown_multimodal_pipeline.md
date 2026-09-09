<!-- codex-research -->
# Image-to-Markdown Multimodal Pipeline Requirements

Selection: A + D1 + G1 + F1 + L1 (approved 2026-09-08).

## Functional requirements

- REQ-001: Provide versioned provider-neutral `ContentPartV1`, `MultimodalRequestV1`, `ModelProfileV1`, `ExtractionDocumentV1`, and `ExtractionReceiptV1` contracts while preserving existing text-only callers.
- REQ-002: Preserve ordered message roles and typed image parts through the existing LLM Caret proxy and provider dispatch; reject models or providers without declared vision capability.
- REQ-003: Support explicit local Slang/OpenAI-compatible and hosted API profiles with model, endpoint, secret reference, image/detail, token, timeout, byte, pixel, concurrency, egress, and fallback settings. Use only the configured provider; never fall back implicitly.
- REQ-004: Run a versioned three-stage prompt protocol: page/region inventory, faithful structured extraction, and consistency audit.
- REQ-005: Classify composable regions as printed text, table, form, highlight/annotation, handwriting, single chart, multiple charts, cell-distribution chart, histogram, line/bar/scatter/area/pie/donut, box/violin/heatmap/contour/scientific, radar/bubble/candlestick/waterfall, treemap/sunburst/funnel/polar/choropleth/density/error-bar, diagram, equation, code, map, photo, screenshot, mixed page, or unknown.
- REQ-006: Transcribe tables/forms into Markdown without inventing cells; preserve row/column spans, missing cells, reading order, source bounds, confidence, and attached highlights/annotations.
- REQ-007: Preserve all detected Unicode scripts without translation. Initial acceptance covers English, Korean, Japanese, Simplified/Traditional Chinese, mixed Latin/CJK numerals, and unresolved/ambiguous glyph markers.
- REQ-008: Extract single-chart and multi-chart structure including panel, axes, scale, units, labels, legend, series, and source bounds.
- REQ-009: Emit high-definition graph numeric arrays. Every value retains its original numeric lexeme when visible and carries observed/calibrated/missing/ambiguous status plus uncertainty; calibrated estimates must never be presented as exact observations.
- REQ-010: Render deterministic human-readable Markdown as the primary dataset artifact, including tables and fenced structured JSON for graph arrays and provenance, plus a separate synchronized evidence receipt.
- REQ-011: Provide an `image-to-markdown` application/service callable through LLM Caret/Codex/Claude proxy routes and an SPipe action that runs only when an image-read model profile is explicitly set.
- REQ-012: Bind SPipe image input, Markdown, structured result, and receipt with stable artifact paths and hashes. Extracted output is observation evidence and cannot serve as its own expected test oracle.
- REQ-013: Provide an automatically discoverable Codex `image-read` skill that selects configured models, follows inventory/extract/audit, preserves uncertainty, and returns Markdown/receipt artifact paths.
- REQ-014: Cache only by source hash plus complete extraction configuration and isolate caches by trust scope; invalidate naturally when any source/model/prompt/schema/preprocessing setting changes.
- REQ-015: Fail closed with typed diagnostics for malformed/unsupported images, unsupported providers, unavailable configured models, unsafe egress, timeout, truncation, invalid structured output, or unresolved required fields.

## Traceability boundary

Provider payload tests prove transport only. Category fidelity and graph accuracy require independent fixture/reference data; generated model output is never accepted as ground truth.
