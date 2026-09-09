<!-- codex-design -->
# Image-to-Markdown multimodal pipeline

This manual mirrors `test/03_system/app/image_to_markdown/feature/image_to_markdown_multimodal_pipeline_spec.spl`. It uses an independent deterministic fixture provider; generated model output is never its own oracle.

## Primary flow

1. Configure an explicit local vision profile. The profile declares vision support, local endpoint, limits, timeout, trust scope, and no fallback. Confirm the canonical `spipe image-read` command routes to the image-read action rather than the unknown-command path.
2. Admit the checked-in 1×1 decoder fixture plus the synthetic Korean
   table/multi-chart, rotated CJK/log-chart, and multilingual laboratory-form
   fixtures. The laboratory page adds a directional flowchart, handwritten
   equation, checkbox states, stamp/seal, highlights, and a captioned photo.
   Verify decoded dimensions and source hashes before any model call. Extract
   the highlighted table while preserving handwriting identity, topology,
   confidence, and highlight attachment.
3. Extract a single-chart image into numeric arrays. Preserve visible numeric
   lexemes, axis ranges/ticks, legend mappings, point-targeted annotations, and
   observed/calibrated/ambiguous status with uncertainty.
4. Extract a multi-panel chart without losing panel identity. Preserve panel
   IDs, shared legends, per-panel ranges, and ordered high-definition arrays.
5. Publish Markdown, structured data, and a synchronized receipt. Bind source/output identity without including image bytes or secrets.
6. Reject unsafe, unsupported, or unconfigured image requests. An unset SPipe profile performs no model call.

## Expected evidence

- Text: deterministic Markdown dataset.
- API: ordered role/content-part payload without raw base64 in logs.
- Artifact: the synthetic fixture manifest, structured extraction, Markdown,
  and receipt files whose hashes are recomputed from disk.
- Log: typed rejection codes and stage timings.

Executable verification is pending a valid admitted self-hosted Simple runtime.
The third bootstrap cleared the earlier C-runtime issue but rejected its Stage
2 candidate during hello-world AOT sanity with `backend object-path status 1`;
see `doc/08_tracking/bug/bootstrap_stage2_backend_object_path_status_2026-09-08.md`.
