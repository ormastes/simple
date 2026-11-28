# Chrome (Blink/Skia) vs Pure-Simple Web HTML Layout Comparison Specification

> Verifies procedural shared asset generation, pure-Simple multi-variation HTML/CSS/Image rendering (`v08`, `v09`, `v10`), parity metrics (`exact`, `<=12`, `<=32`, `MAD`, `4x |diff|`), and SDN comparison report emission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Category | Application |
| Status | Active |
| Requirements | REQ-WEB-008 |
| Plan | `doc/03_plan/sys_test/simple_web_engine_completion.md` |
| Source | `test/03_system/app/simple_web/feature/chrome_vs_simple_web_layout_compare_spec.spl` |
| Updated | 2026-11-28 |

## Scenarios

1. **Procedural shared image asset synthesis (`sunset`, `avatar`, `cube`, `star`):** Verifies `compare_default_resources()` emits 4 `SimpleOsHostGpuImageResource` entries matching `../assets/{sunset,avatar,cube,star}.png` at `160x96`, `48x48` (with transparent corners), `120x80`, and `20x20`.
2. **Multi-variation pure-Simple software rendering (`v08`–`v10`):** Renders `v08` (positioned pills/overlay/z-index), `v09` (inline typography/code pills/text-align), and `v10` (flex-wrap chips & card grid) at `520x340` via `simple_web_layout_render_html_software_pixels_with_images` + `encode_argb_to_png_rgb`, asserting exact buffer dimensions, multi-color diversity, and valid PNG headers.
3. **Pixel parity & SDN report emission:** Validates `compare_compute_parity` exact/near-12/near-32/MAD metrics + `4x |diff|` heatmap generation and verifies `compare_format_report_sdn` produces canonical SDN tables (`summary`, `variations`).
