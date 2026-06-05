# Low Dependency UI dynSMF Feature Requirement Options

Date: 2026-06-05

No final requirements are selected yet. The user must choose one option or a
combination before `doc/02_requirements/feature/low_dependency_ui_dynsmf.md` is
written.

## Option A: Boundary-First Refactor

Description: First split UI contracts from renderer implementations and add
dependency-boundary tests. dynSMF stdlib loading follows after the UI graph is
measurably smaller.

Pros:

- Lowest risk to existing GUI/web behavior.
- Gives immediate proof that TUI does not depend on GUI/HTML/CSS implementation.
- Produces clean seams for dynSMF packaging.

Cons:

- Does not deliver default dynSMF stdlib loading in the first implementation
  tranche.
- Requires a second tranche for startup policy and loader integration.

Effort: Medium.

## Option B: dynSMF-First Loader Feature

Description: Add manifest-driven precompiled dynSMF loading, opt-out controls,
and unload/reload session APIs first, then migrate UI/render libraries onto the
loader.

Pros:

- Directly addresses the new runtime capability.
- Gives interpreter tests an unload/reload primitive early.
- Existing dynlib tests and GUI dynlib probes provide a starting point.

Cons:

- May package current UI dependencies before they are minimized.
- Higher risk of preserving bad dependency shape behind dynSMF manifests.

Effort: Medium-high.

## Option C: Thin Vertical Slice

Description: Implement one complete low-dependency dynSMF slice for TUI and one
HTML-capable GUI widget, including manifests, opt-out, unload/reload tests, and
dependency closure checks.

Pros:

- Proves the whole architecture with bounded blast radius.
- Produces executable examples for later file IO, net IO, 2D, web, GUI, and TUI
  library migration.
- Balances architecture validation with implementation evidence.

Cons:

- Leaves some stdlib-like libraries as planned follow-up until the pattern is
  validated.
- Requires careful test naming so the slice is not mistaken for full migration.

Effort: High.

## Option D: Full Parallel Migration

Description: In one coordinated phase, split UI contracts and package file IO,
net IO, 2D renderer, web renderer, GUI renderer, and TUI renderer as dynSMF
libraries with default autoload and per-library opt-out.

Pros:

- Closest to the complete requested end state.
- Avoids temporary mixed architecture lasting across many iterations.

Cons:

- Highest conflict risk in the shared checkout.
- Requires broad verification across compiler, loader, UI, GUI, web, and
  platform tests.
- More likely to collide with concurrent LLM lanes.

Effort: Very high.

## Recommended Selection

Option C is the best first selected requirement set: it proves the complete
architecture with real code while limiting the number of simultaneously edited
UI/render libraries.
