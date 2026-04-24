# svim Feature Options

## Option A — Shared Core With Host TUI First

- Pros: matches the supplied plan, establishes reusable session API early, avoids duplicating editing logic across host and OS shells.
- Cons: initial user-visible UI is modest while core surfaces stabilize.
- Effort: medium-high.

## Option B — SimpleOS Shell First

- Pros: integrates directly with the existing OS app surface.
- Cons: couples editor bring-up to WM/app integration before the core is stable; slower feedback loop for host tests.
- Effort: high.

## Option C — Patch Legacy `src/os/apps/editor/editor.spl`

- Pros: smallest short-term patch count.
- Cons: preserves the wrong architecture, keeps rendering and editing intertwined, blocks clean reuse by future shells.
- Effort: low short-term, high long-term migration cost.

## Selected

Option A is selected by the supplied implementation plan.
