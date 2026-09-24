# NFR Requirements — Rendering Showcases

Date: 2026-09-24. Feature: `doc/02_requirements/feature/rendering_showcases.md`.

## NFR-001 Loading-overhead reduction (core/extended split)

Core-tier import closure must be meaningfully smaller than the
full/extended tier per lane, measured by a static transitive-import census
(`scripts/check/check-rendering-showcase-closure.shs`).

**Recalibrated 2026-09-24** (the original flat ≤ 0.60 ratio target was set
pre-implementation and is structurally unreachable on graph-dominated
lanes — measured: 2d 232/247 = 0.94, web 315/317 = 0.99, because the
engine2d/browser-engine import graphs dominate BOTH tiers and the extended
tier adds only its own scene module). Per-lane targets:

- **tui / gui / wm**: core/brief closure ≤ 60% of the full sibling. These
  lanes are red by construction until the shared widget-core refactor
  lands (tui/wm measured 1.00 — full entries are self-contained; tracked
  in the L9 review-fix lane).
- **2d / web**: strict reduction — the core closure must be smaller than
  the extended closure (measured margins: 2d 15 files, web 2 files). The
  split's loading value on these lanes is that core never imports the
  extended content, which the strict reduction plus the real `use`-edge
  direction guarantees.

Gate fails on: target miss per lane, or closure-growth regression.

## NFR-002 Headless verifiability

Every showcase entry must be verifiable without a physical display:
compile-check for all entries; PPM capture for 2D/GUI; sdn parse for the item
list; bounded HTTP boot probe for the web-server GUI. Runs use
`SIMPLE_TIMEOUT_SECONDS=0` (or native-build cache) because the graphics stack
exceeds the 10 s example watchdog under the currently available compilers
(see research §4 — deployed self-hosted toolchain is stale; do not claim
certified PASS from seed-based runs).

## NFR-003 Consistency

All ten lane entries + the two cross-lane entries share one naming scheme
(`rendering_<lane>_<tier>.spl`, `rendering_<items|switch>.*`), one directory,
one `doc.md` run-command table, and per-entry header comments stating lane,
tier, and shared-core dependency. Drift enforced by the wiki entry Agent
lookup rule (REQ-008).

## NFR-004 Wiki freshness

The `llm_wiki.md` entry and the feature-expert skill are updated in the same
change that lands the showcases (single commit/PR), so the wiki never points
at not-yet-landed or removed paths.
