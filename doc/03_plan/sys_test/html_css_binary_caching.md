<!-- codex-research -->

# HTML/CSS Binary Caching Test Plan

- Unit: `test/unit/app/ui/web_render_backend_api_spec.spl` verifies static-shell classification, dynamic-island detection, stable cache key propagation, and prebuilt full-HTML IPC generation.
- Scripted comparison: `scripts/check-gtk-gui-size-speed-baseline.shs` records Simple render-loop speed and GTK baseline data where available.
- Static check: run `bin/simple check src/lib/common/ui/web_render_api.spl`.
- Targeted unit check: run `SIMPLE_LIB=src bin/simple test test/unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`.

Traceability:

- REQ-HCBC-001 through REQ-HCBC-005: unit spec.
- REQ-HCBC-006 through REQ-HCBC-007: GTK comparison script/report.
- NFR-HCBC-001 through NFR-HCBC-005: code review, targeted checks, and script output.
