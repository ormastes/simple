# Shared retained DrawIR frame-owner evidence — 2026-08-12

Status: **CORRECTNESS PASS / BASE LANE IMPLEMENTED / 8K80 NOT PROVEN**

`RetainedDrawIrFrame` is a backend-neutral shared owner for Web, GUI and WM
frame switching. It stores canonical DrawIR commands, accepts one full seed,
then applies `DrawIrDeltaResult` patches through zero-full-copy in-place replay.
It owns no producer semantics, backend state, GPU cache, or transient atlas.

Every transition emits an exact receipt: full seed, patch, idle, or rejected;
command count; command writes; frame generation; and reason. Patch admission
requires the retained command count to remain stable and changed indices to be
valid, strictly ascending and unique. Rejected deltas perform zero writes.

Patch receipts also capture damage before retained mutation. Rects, images and
resolved text emit clipped old-plus-new bounds; this preserves both the vacated
and newly painted regions for moves/resizes. Unresolved text, paths, edges,
groups and other commands without proven bounds conservatively select the full
viewport. Idle and rejected frames emit no damage. These are damage candidates
for the shared tile planner, not an approximate occlusion mask.

Focused coverage passed: four-command seed, exactly one command write for a
one-component delta, zero writes for the settled frame, and five cumulative
writes across all three frames. Unseeded, duplicate, unsorted and count-changing
deltas were rejected without retained-state mutation. O3 analysis completed
with 27 further opportunities.

This closes the shared frame-owner/base implementation seam. Producer-specific
adoption remains pending because WM/Web/GUI owner files are concurrently
modified. No native 7680x4320 p50/p95/RSS/checksum row was produced, so this
does not establish 8K/80.
