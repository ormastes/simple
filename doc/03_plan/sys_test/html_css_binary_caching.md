<!-- codex-research -->

# HTML/CSS Binary Caching Test Plan

- Unit: `test/unit/app/ui/web_render_backend_api_spec.spl` verifies static-shell classification, dynamic-island detection, stable cache key propagation, and prebuilt full-HTML IPC generation.
- Unit: `test/unit/app/ui/web_render_cache_spec.spl` verifies persistent static-shell storage, dynamic-island persistence bypass, in-memory hot cache hits, compact static-shell binary-plan sizing, decoded layout payload fields, decode validation, prepared SWBC reuse, and retained command payload reuse.
- Scripted comparison: `scripts/check/check-gtk-gui-size-speed-baseline.shs` records Simple render-loop speed and GTK baseline data where available.
- Static check: run `bin/simple check src/lib/common/ui/web_render_api.spl`.
- Static check: run `bin/simple check src/app/ui.web/render_cache.spl`.
- Targeted unit check: run `SIMPLE_LIB=src bin/simple test test/unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`.
- Targeted unit check: run `SIMPLE_LIB=src bin/simple test test/unit/app/ui/web_render_cache_spec.spl --mode=interpreter`.

Traceability:

- REQ-HCBC-001 through REQ-HCBC-005: unit spec.
- REQ-HCBC-006 through REQ-HCBC-007: GTK comparison script/report.
- REQ-HCBC-008 through REQ-HCBC-011 and REQ-HCBC-013 through REQ-HCBC-015: render cache unit spec.
- REQ-HCBC-012: GTK comparison script/report.
- NFR-HCBC-001 through NFR-HCBC-007: code review, targeted checks, and script output.
