<!-- codex-design -->
# Image-to-Markdown Multimodal Pipeline System Test Plan

## Purpose

Provide executable evidence for the deterministic requirements and explicit
evaluation procedures for model-dependent accuracy/resource requirements.
Model output is an observation; checked-in reference topology/text/numeric
samples are the oracle. A requirement is not marked proven merely because it
appears in the file-level `@req` declaration.

## Requirement trace matrix

| Requirements | Executable assertion or evidence | Current gate |
|---|---|---|
| REQ-001, REQ-002, NFR-007 | `check_ordered_multimodal_parts_preserved`, proxy model-selection/role-part tests, plus legacy proxy suite | Executable + external suite |
| REQ-003, REQ-011, REQ-015, NFR-001, NFR-003, NFR-008 | `check_no_model_call_occurred`, `check_safe_typed_failure`, typed timeout/truncation unit scenarios | Executable source evidence; runtime proof pending |
| REQ-004, REQ-005 | canned inventory/extract/audit stage IDs and category validation | Executable |
| REQ-006, REQ-007 | `check_table_topology_and_annotations`, `check_original_scripts_preserved` | Executable |
| REQ-008, REQ-009 | `check_graph_samples_and_uncertainty`, `check_multi_panel_identity` | Executable |
| REQ-010, REQ-012 | `check_markdown_matches_reference`, `check_receipt_artifact_hashes` | Executable |
| REQ-013 | `check_canonical_spipe_image_read_command_registered`, skill discovery and compiled action-surface check | Source registered; compile/runtime proof pending |
| REQ-014 | cache-key/revision/trust/secret-reference identity plus digest-corruption rejection | Executable unit source evidence; runtime proof pending |
| NFR-002, NFR-012 | bounded admission plus deterministic provider call-count assertion (`1`) | Executable source evidence; runtime proof pending |
| NFR-004, NFR-009 | warm timing/RSS performance spec and receipt timing assertions | Partial; trusted provider-side inference timing pending |
| NFR-005 | acceptance-corpus parse/validation report, denominator and model revision | Model evaluation; pending configured run |
| NFR-006 | receipt hash plus prompt/extraction-schema/preprocessing/renderer-version, safe-error, request/cache, provenance-count, and validation-count assertions | Executable source evidence; runtime proof pending |
| NFR-010, NFR-011 | fixture corpus report, private-image recipe, Markdown review | Manual/evaluation evidence |

## Primary scenario

The executable manual at `test/03_system/app/image_to_markdown/feature/image_to_markdown_multimodal_pipeline_spec.spl` uses the frozen steps and helpers from the detail design. It configures a local-only vision profile, verifies ordered multimodal parts, extracts a highlighted Korean/English table, renders one observed/calibrated graph, preserves two chart panels and a shared legend, and validates artifact/receipt bindings.

## Negative matrix

- missing profile, text-only capability, forbidden remote egress, or non-empty fallback;
- unsupported MIME, invalid dimensions/hash/detail, excessive image count/pixels/bytes;
- malformed/oversized structured response, table topology mismatch, unknown region reference;
- observed chart value without a visible lexeme, calibrated value without uncertainty/method;
- timeout, truncation, unsafe image URL, path outside permitted roots, and cache trust-scope mismatch.

## Independent corpus

Checked-in synthetic fixtures under `test/fixture/image_to_markdown/` cover a
highlighted table with Korean handwriting, Japanese/Chinese text, rotation,
low contrast, one chart, multiple panels, a cell-distribution graph, a log
axis, overlap, a missing legend, and an ambiguous graph value. The independent
`README.md` records source hashes and expected visible content.

For private-real evaluation, copy images into a non-repository directory,
record only SHA-256, dimensions, category labels, aggregate field accuracy,
structured-parse rate, latency, and peak RSS, and delete temporary Markdown
whenever its contents cannot be retained. Never publish source pixels, raw
extractions, paths containing personal data, or model credentials.

## Evidence

Capture the rendered Markdown (`text`), normalized provider payload (`api`), structured document/receipt (`artifact`), validation diagnostics (`log`), and measured timing/RSS (`exec`). Generate the mirrored manual with `spipe-docgen`; primary flow must be visible and executable code folded.

## Gates

- Every requirement has a direct assertion or trace entry.
- Existing text-only Caret proxy goldens remain green.
- Numeric arrays compare label association, sample count, lexemes, values/tolerance, status, uncertainty, and panel identity.
- Warm preprocessing/proxy p95 is below 100 ms excluding inference/network.
- No secrets, raw image bytes, or data URLs appear in logs/evidence.
