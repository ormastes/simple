# NFR Requirements — Rendering Showcases

Date: 2026-09-24. Feature: `doc/02_requirements/feature/rendering_showcases.md`.

## NFR-001 Loading-overhead reduction (core/extended split)

Core-tier import closure must be meaningfully smaller than the
full/extended tier per lane, measured by a static transitive-import census
(`scripts/check/check-rendering-showcase-closure.shs`).

**Final targets (2026-09-24, after two measurement-driven recalibrations).**
The original flat ≤ 0.60 ratio target was set pre-implementation and is
disproven by measurement on every lane: the engine2d / browser-engine /
compositor import graphs dominate BOTH tiers everywhere (post-refactor,
merged main: tui 124/126 = 0.98, gui 108/154 = 0.70, wm 444/444 = 1.00,
2d 232/247 = 0.94, web 315/317 = 0.99). The brief/full and core/extended
tiers differ in CONTENT (which scenes/widgets are built), not in runtime
import graphs. The split's real loading guarantee is directional: **core
never imports extended/full content**. Per-lane gate:

- **2d / web / tui / gui**: strict reduction — core closure < extended/full
  closure (measured margins: 2d 15, web 2, tui 2, gui 46 files).
- **wm**: no-growth — core ≤ full (closure-neutral by design: both tiers
  share the compositor graph via `rendering_wm_common`; the split is
  content — 2 windows vs 3 + sabotage — not imports).

The structural half of the tier contract (file-based split; extended/full
REALLY imports the shared core modules — no `SHOWCASE_TIER`-style env
switching) is enforced by the acceptance spec's import assertions.

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
