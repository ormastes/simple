# WebRenderer Retained Damage Plan Evidence — 2026-08-12

Status: **CORRECTNESS PASS / STRUCTURAL IMPROVEMENT / 8K80 UNPROVEN**

The canonical web tile lane feeds semantic/layout-owned `DamagePlan` rectangles
and flat `DrawIrCommand` arrays directly to Engine2D; no WebIR or DrawIR schema
copy is introduced. Retained replay previously called
`engine2d_draw_ir_coalesce_plain_fills` once for every damage rectangle. The
coalesced command arrays and logical receipt weights depend only on the immutable
display list, so the flat retained executor now builds one plan per frame and
reuses it for every exact clip.

The focused disjoint-damage scenario passed. Two adjacent logical fills coalesce
to one physical command, replay through two non-overlapping damage rectangles,
preserve the logical rendered count of four, and match the exact whole-buffer
pixel oracle. The encompassing DrawIR spec reported 50/58 scenarios passing;
the eight failures are existing image/CSS-background/runtime issues outside this
planning change.

Scope is deliberately narrow: flat retained WebRenderer/DrawIR replay benefits.
Multi-batch composition replay still plans each batch inside each damage clip;
a struct-plan-array trial was functionally correct but did not produce
defensible performance evidence and was not retained. No 8K timing row is claimed:
the required no-stub self-hosted executable remains blocked by the measured
interpreted entry-closure build path, which produced no objects before its
300-second watchdog. Seed/interpreter timing is not promoted as production
WebRenderer evidence.
