<!-- codex-research -->
# Image-to-Markdown Multimodal Pipeline — Domain Research

## Findings

- Modern vision APIs accept ordered text and image content parts. OpenAI accepts URL, file, or base64 data-URL image inputs and an explicit `detail` level; this supports a single provider-neutral image descriptor mapped by adapters. Source: https://platform.openai.com/docs/api-reference/responses
- Anthropic's vision interface likewise treats images as typed message content, reinforcing that raw provider JSON should remain below a shared typed request. Source: https://docs.anthropic.com/en/docs/build-with-claude/vision
- Ollama supports image inputs for vision models, making an OpenAI-compatible/local path practical, but capability detection must fail closed when the configured model is text-only. Source: https://docs.ollama.com/capabilities/vision
- DePlot demonstrates that chart understanding improves when chart pixels are first translated to an underlying table, then reasoned over. This supports requiring numeric arrays/tables as first-class output rather than accepting only narrative Markdown. Source: https://aclanthology.org/2023.findings-acl.660/
- Table Transformer separates table detection and structure recognition. Even when a general vision LLM is used, evaluation should separately score table boundaries, cells, spans, and content. Source: https://arxiv.org/abs/2110.00061
- PaddleOCR documents multilingual OCR and document parsing components. Handwriting and local-language output must preserve original script, language guesses, reading order, and uncertain glyphs rather than silently translating. Source: https://www.paddleocr.ai/

## Category taxonomy

Minimum categories should be: `document_text`, `table`, `form`, `highlighted_text`, `handwriting`, `single_chart`, `multi_chart`, `cell_distribution_chart`, `diagram`, `equation`, `mixed_page`, and `unknown`. Categories are composable because one page may contain several regions.

Chart subtypes should cover line, bar/grouped/stacked bar, scatter, area, histogram, box/violin, pie/donut, heatmap, and mixed/unknown. Multi-chart output must preserve panel identity and shared-axis/legend relationships.

## Three-stage extraction contract

1. **Inventory:** classify the page and enumerate regions/panels, languages, visible highlights, axes, legends, and reading order.
2. **Extract:** emit faithful Markdown plus structured tables, text spans, and chart numeric arrays with units, labels, panel IDs, and source pixel bounds.
3. **Audit:** cross-check counts, table shape, series lengths, axis scale/range, missing/occluded values, and confidence; explicitly mark inferred values.

This staged contract is more testable than a single prose prompt and permits a high-resolution re-read/crop only for uncertain regions.

## Dataset format conclusion

Markdown should be the human-readable primary artifact, with stable headings, tables, fenced `json` blocks for graph arrays and provenance, and image-region links. A small structured receipt should record schema version, source hash, model/provider, prompt version, dimensions, regions, confidence, warnings, and whether values are observed or inferred.

## Evaluation implications

Use exact/normalized text metrics for OCR, cell-level precision/recall and topology for tables, language/script preservation for handwriting, highlight region overlap plus text accuracy, and series/axis metrics for charts (numeric tolerance, label association, point count, and panel completeness). Visual quality must be tested on held-out real images, not only mocked API responses.

## Taxonomy extension (2026-09-08)

The extraction taxonomy is composable rather than mutually exclusive. Beyond
text/table/form and single/multiple graphs, inventory distinguishes
histogram/cell-distribution, line, bar, scatter, area, pie/donut, box/violin,
heatmap, contour and scientific plots; flowcharts, networks, schematics and
timelines/Gantt; equations, chemical structures and musical notation;
signatures, stamps/seals, maps, code, photos, screenshots, and barcode/QR
marks. This preserves secondary roles such as handwriting annotating a heatmap
inside a mixed page.

The analytical-chart extension also distinguishes radar, bubble, candlestick,
waterfall, treemap, sunburst, funnel, polar, choropleth, density, and error-bar
views. Where the v2 point contract has no dedicated higher-dimensional or
hierarchical field, fidelity requires aligned named measure series and explicit
relationship annotations; silently collapsing those measures into one x/y
curve would lose evidence.
