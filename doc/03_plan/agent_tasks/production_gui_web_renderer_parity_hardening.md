# Production GUI Web Renderer Parity Hardening Agent Tasks

## Parallel Audit Completed

- Renderer infrastructure audit: identify real pixel comparison harnesses,
  dummy/sentinel tests, and production parity gaps.
- Web/widget renderer audit: identify heuristic routing, exact fixture
  branches, CSS/layout gaps, and generated HTML escaping risks.
- SPipe artifact audit: identify requirement, architecture, design, spec, and
  manual paths.

## Current Implementation Slice

- Add marker-free generated GUI widget parity harness.
- Route generated widget HTML through the generic layout renderer.
- Add generic image fallback rendering in the layout renderer.
- Add executable SPipe system spec for software, CPU SIMD, and Metal exact
  backend parity.

## Next Agent Tasks

- Add live Electron/WebKit capture manifest and exact pixel runner.
- Add CPU SIMD counter evidence to the parity report.
- Add Metal GPU-readback provenance to reject CPU mirror fallback.
- Expand CSS/layout matrix for width, height, margin, padding, border, flex,
  gap, and nested selectors.
