# Bug: Production GUI font offload lacks runtime glyph readback

Status: fixed
Date: 2026-06-23
Fixed: 2026-07-02
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
- `production_gui_font_offload_runtime_evidence_status=pass`
- `production_gui_font_offload_vector_production_ready=true`
- `production_gui_font_offload_bitmap_production_ready=true`
- vector and bitmap actual checksums match their expected checksums
- the wrapper is driven by real runtime/backend evidence, not synthetic env-only
  readiness values

## Resolution Evidence

Fixed by the macOS Metal vector/bitmap font readback lane. Live evidence from
`build/font-offload-metal-after-fix/report.md` reported:

- `production_gui_font_offload_status=pass`
- `production_gui_font_offload_reason=vector-and-bitmap-font-readback-matched`
- `production_gui_font_offload_runtime_evidence_status=pass`
- `production_gui_font_offload_vector_backend=metal`
- `production_gui_font_offload_vector_readback_status=vector-font-glyph-readback-matched`
- `production_gui_font_offload_vector_production_ready=true`
- `production_gui_font_offload_bitmap_backend=metal`
- `production_gui_font_offload_bitmap_readback_status=gpu-glyph-raster-readback-matched`
- `production_gui_font_offload_bitmap_production_ready=true`

The full desktop production aggregate in
`doc/09_report/production_gui_web_renderer_parity_evidence_2026-07-02.md`
also reports `production_gui_web_renderer_parity_status=pass` with
`production_gui_web_renderer_parity_font_offload_status=pass`.

## Notes

Related historical evidence is in:

- `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-16.md`
- `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-21.md`
