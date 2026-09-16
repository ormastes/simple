# Bug: Production GUI font offload lacks runtime glyph readback

## Triage note 2026-09-13 — not verifiable on this host; left OPEN, not stale
- **measured**: every product path this entry references still exists in the tree, so there is no removed-code / dead-reference basis for closing it stale.
- **inferred**: reproduction needs a Linux host with a GPU, RenderDoc, and/or Electron/Chrome Vulkan backing. This triage host is Windows with no such lane, and `bin/simple` here is the Rust seed (v1.0.0-rc.1), not the self-hosted binary these evidence gates are written against.
- **inferred**: "does not run on Windows" is not evidence of a fix, so no closure is claimed. The gate remains blocked until re-run on the Linux evidence lane.

Status: open
Date: 2026-06-23
Area: GUI/web renderer parity, Engine2D font offload

## Symptom

Production GUI/web renderer parity remains incomplete when the font-offload
gate reports:

- `production_gui_web_renderer_parity_gate_font_offload_status=unavailable`
- `production_gui_web_renderer_parity_gate_font_offload_reason=vector-font-gpu-glyph-return-missing;runtime-unavailable`

The gate must stay failed until both vector and bitmap font evidence prove real
accelerator submission and glyph/mask readback. A software checksum or fallback
bitmap is not production font-offload evidence.

## Required Evidence

Use `scripts/check/check-production-gui-font-offload-evidence.shs`. Completion
requires:

- `production_gui_font_offload_status=pass`
- `production_gui_font_offload_vector_production_ready=true`
- `production_gui_font_offload_bitmap_production_ready=true`
- vector and bitmap actual checksums match their expected checksums
- the wrapper is driven by real runtime/backend evidence, not synthetic env-only
  readiness values

## Notes

Related historical evidence is in:

- `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-16.md`
- `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md`
