# Simple Browser Design Effects Compatibility Audit

Date: 2026-05-06

Scope: 10 deterministic design/effect examples inspired by current design inspiration and effects categories: Awwwards, CSS Design Awards, Dribbble, Behance, Mobbin, Godly, Siteinspire, GSAP, Three.js, and JS/CSS class-toggle effects.

Reference sources: Colorlib 2026 design inspiration roundup, Awwwards, CSS Design Awards, FreeFrontend GSAP examples, and HTMLHub effect categories.

Viewport: 80x50
Checks: 30
Exact checks: 30/30
Failures: 0

## Top Differences

| Rank | Example | Source | State | Diff px | Match/10000 | Max channel diff | SAD | Exact |
|---:|---|---|---|---:|---:|---:|---:|---|
| 1 | Awwwards-style hero reveal | Awwwards | start | 0 | 10000 | 0 | 0 | true |
| 2 | Awwwards-style hero reveal | Awwwards | final | 0 | 10000 | 0 | 0 | true |
| 3 | Awwwards-style hero reveal | Awwwards | chrome-js-final-vs-static-final | 0 | 10000 | 0 | 0 | true |
| 4 | CSS Design Awards-style panels | CSS Design Awards | start | 0 | 10000 | 0 | 0 | true |
| 5 | CSS Design Awards-style panels | CSS Design Awards | final | 0 | 10000 | 0 | 0 | true |
| 6 | CSS Design Awards-style panels | CSS Design Awards | chrome-js-final-vs-static-final | 0 | 10000 | 0 | 0 | true |
| 7 | Dribbble-style shot grid | Dribbble | start | 0 | 10000 | 0 | 0 | true |
| 8 | Dribbble-style shot grid | Dribbble | final | 0 | 10000 | 0 | 0 | true |
| 9 | Dribbble-style shot grid | Dribbble | chrome-js-final-vs-static-final | 0 | 10000 | 0 | 0 | true |
| 10 | Behance-style case study | Behance | start | 0 | 10000 | 0 | 0 | true |

## Notes

- `start` compares Chrome start-state pixels to Simple start-state pixels.
- `final` compares Chrome settled/final-state pixels to Simple settled/final-state pixels.
- `chrome-js-final-vs-static-final` verifies that the synchronous JavaScript class-toggle fixture reaches the same final Chrome pixels as the static final state before using the static final state for Simple comparison.
- The fixtures avoid text rendering so this is a strict pixel/color check for layout and effect state colors without font-antialiasing noise.
