# Bug: Production GUI font offload lacks runtime glyph readback

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
