# NFR Requirements — Rendering Showcases

Date: 2026-09-24. Feature: `doc/02_requirements/feature/rendering_showcases.md`.

## NFR-001 Loading-overhead reduction (core/extended split)

Core-tier module closure compiles ≤ 60% of the full/extended-tier module
count per lane. Measured by a closure census (same style as
`scripts/check/check-ui-slim-closure.shs`) over
`rendering_{tui,gui,2d,web}_{core,full|extended}.spl`. Verification: one
script under `scripts/check/` emits both counts and the ratio; gate fails
above 0.60 or on closure-growth regression.

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
