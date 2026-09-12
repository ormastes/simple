# Compound attribute selectors evaluated only their FIRST bracket group (2026-09-12)

**Status:** FIXED.
**Component:** pure-Simple web renderer, selector matcher.
**Severity:** blanked 7 of the 8 shared catalog tabs.

## Defect

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:1312-1319`
(`simple_match`) read `attr_start = text_index_of(base, "[")` and
`attr_end = text_index_of(base, "]")`, tested that ONE `[`…`]` group with
`attr_selector_matches`, and discarded the rest of `base`.

Every catalog tab carries `[role="tabpanel"][hidden] { display: none; }`. The
matcher evaluated only `role="tabpanel"`, ignored `[hidden]`, and applied
`display:none` to the *visible* panel — the only child of `<main>` — so the
document collapsed to the body background. Measured `distinct_colors = 1` over
684,000 px on seven of eight tabs.

`attr_selector_matches` itself (`:1106-1145`) was correct, including bare-`[name]`
presence semantics; the defect was entirely in this caller.

## Fix

Loop every bracket group from `attr_start` to the end of `base`; all must match
(capped at 32 groups). ~20 lines, same file.

## Specs

Both in `test/unit/browser_engine/compound_attribute_selector_spec.spl` (mirrored
into `test/01_unit/browser_engine/`), absolute pixel oracles on a 300x200 frame:

- **Reproducing** — `describe "compound attribute selector — all groups must match"`:
  `[role=tabpanel][hidden]{display:none}` must leave an un-hidden panel visible
  (pixel (50,50) == `0xff0000`), and must still hide one that IS `hidden`
  (== `0xffffff`).
- **Generalization** — `describe "compound attribute selector — [a][b] needs both
  attributes"`: `[data-a][data-b]` matches when both attributes are present and
  does NOT match when only the first is.

## Sabotage verification

Re-limiting the new loop to one group (`group_count < 1`) turned the spec file
from `4 examples, 0 failures` to `2 passed / 2 failed`; restoring it returned
`4 examples, 0 failures`. Green → red → green, all three runs on the same tree
and binary (seed `src/compiler_rust/target/bootstrap/simple`).

## Evidence

Diagnosis: `doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`.
