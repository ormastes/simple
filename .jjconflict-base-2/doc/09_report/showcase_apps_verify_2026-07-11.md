# Showcase apps verification — 2026-07-11

## Result

STATUS: FAIL

## Accepted evidence

- Canonical catalog contains exactly three stable identities and an explicit 3x3 readiness matrix.
- The GUI widget showcase has existing real standalone and filesystem-child host-WM rendering/input paths.
- The new web standards page covers common semantic, layout, table, form, responsive, overflow, canvas/SVG, and media probes.
- The new 2D source invokes the public Engine2D primitive families, composition, clip/mask, present, and provenance readback.
- UI and SPipe guidance rejects blank, dummy, source-only, and synthetic-handle evidence.
- Typed catalog action parsing rejects malformed, unknown, and currently blocked app/surface requests.
- A 3x3 executable SPipe source and mirrored source-ready manual now fail explicitly until production launch/evidence wrappers exist.

## Release blockers

- `graphics_2d_showcase` terminates at the shared Engine2D creation/trait-boxing boundary; an existing Engine2D example fails identically. Constructor reuse hazards were fixed, but the deployed self-host still exits 132 before evidence.
- `web_standards_showcase` terminates before its runner begins after argv/env and unique UI-import dependencies were removed. The renderer is not reached.
- Production-reachable browser paths still contain white/striped URL output, canned WM Browser HTML, degraded tag-stripped SimpleOS pixels, and legacy hardcoded browser content.
- Host-WM adapters are missing for graphics and web.
- Installed SimpleOS launcher/package/WM integration is missing for all three showcases.
- The catalog app semantic spec was corrected after its first focused run but has not received a fresh final run.
- SPipe doc generation remains blocked by the independent checker/parser runaway; the mirrored manual does not claim generated `0 stubs`.

Catalog readiness remains false for every unproven surface.
