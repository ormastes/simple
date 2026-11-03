# TUI list retains stale scroll offset after viewport growth

Status: source repair; runtime verification unexecuted by explicit user waiver.

The canonical `nogc_sync_mut/tui/widgets/list.spl` owner only scrolled toward
selection. A five-item list selected at index 4 in a two-row viewport kept offset
3 when expanded to four rows, rendering d/e and two blanks instead of b/c/d/e.
Clearing selection bypassed normalization altogether. Public negative offsets
could also index before the first item.

The repair clamps the offset to the available viewport range regardless of
selection, ignores invalid selections for scrolling, and resets non-positive
height viewports to offset zero while retaining selection. Reopening scrolls
the retained selection into view.

Regression specification: `test/01_unit/lib/nogc_sync_mut/tui/list_viewport_bounds_spec.spl`.
Covers viewport growth, cleared selection, collapsed/reopened viewports,
negative offsets and an emptied item collection. No build, compiler check,
test execution or live terminal check was performed. Static review and diff
checks do not establish runtime correctness.
