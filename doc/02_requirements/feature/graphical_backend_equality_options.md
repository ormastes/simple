# Graphical Backend Equality — Feature Requirement Options

Date: 2026-06-03

Status: options only. User selection is required before final requirements.

## Option A — WM Compare Contract First

Build a common graphical equality contract inside `wm_compare` first:
`RenderCase`, `GraphicalBackendSpec`, normalized capture metadata, equality
report, and SPipe specs over the existing exact/threshold comparison helpers.

Pros:
- Lowest risk because it extends the existing `wm_compare` measurement and
  failure-report stack.
- Immediately improves Electron/Simple/Web/WM evidence.
- Keeps the first refactor scoped to tests and app-level comparison tooling.

Cons:
- Engine2D backend and web/GUI adapters may still need thin bridge code later.
- Shape/color perceptual metrics would initially be represented as policy
  fields and diagnostics, not a complete production diff engine.

Effort: medium.

## Option B — Engine2D + WM Unified Test Facade

Create a shared test facade that spans Engine2D backend parity and `wm_compare`
capture/equality, then update selected tests to render the same canonical cases
through both surfaces.

Pros:
- Directly addresses equivalent drawings across graphical and backend tests.
- Reduces duplicate fixtures between `test/integration/rendering` and
  `test/system/wm_compare`.
- Establishes the common interface needed for future CPU/Vulkan/Metal/Web/GUI
  matrix expansion.

Cons:
- Higher coordination cost across rendering and WM/web ownership boundaries.
- Requires careful migration to avoid breaking completed shared-WM contracts.

Effort: high.

## Option C — Full Graphical Regression Infra

Implement the full external proposal: backend selector URI, capability flags,
capture kinds, geometry metadata, analytic/reference oracles, shape/color diff
metrics, artifact writer, and HTML report.

Pros:
- Most complete long-term architecture for CPU/GPU/Web/GUI/WM equality.
- Best diagnostic output for production graphical regressions.
- Cleanly supports platform-specific native chrome and titlebar policies.

Cons:
- Too large for one safe refactor unless split into several subfeatures.
- Requires additional image-processing/color-metric implementation decisions.
- More likely to touch hot GUI/renderer paths and need broader verification.

Effort: very high.

## Required Selection

Select one option before implementation. Recommended next slice is Option A or
Option B; Option C should be decomposed after one of those proves the contract.
