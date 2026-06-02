# Production GUI Web Renderer Parity Hardening Design

## Data Model

`ProductionGuiWebParityReport` records:

- generated HTML and provenance flags;
- resolved software, CPU SIMD, and Metal backend names;
- framebuffer sizes and software color diversity;
- exact comparison metrics for CPU SIMD and Metal against software;
- tolerance policy and aggregate exact-parity status.

## Renderer Changes

`simple_web_engine2d_renderer` now forces generated widget HTML through the
generic layout renderer before heuristic fixture detection. This prevents real
GUI HTML from being accepted by legacy substring shortcuts.

`simple_web_html_layout_renderer` now has generic `img` replaced-element
fallback painting in addition to existing button and text painting.

## Test Design

The system spec builds widget HTML with text, image, and icon button content,
then asserts marker-free provenance, non-empty pixels, color diversity, and
exact backend parity for software, CPU SIMD, and Metal.
