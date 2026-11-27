# Persistent manual smux geometry

Status: one authored implementation candidate; Phase 3 compilation, runtime
execution and SPipe generation pending. No new compiler build was run.

The split API previously resized pane dimensions then discarded coordinates by
marking the window manual. Both interactive `current` layout and attachment
frame reflow replaced manual windows with tiled layout. Horizontal and nested
splits therefore changed direction or position on the next client request.

The existing service window now owns manual pane rectangles and their reference
canvas. No second client registry or recursive split-tree owner is introduced.
Named layouts keep their existing gapless geometry. A manual split divides only
the addressed rectangle using the existing one-cell separator contract and
leaves sibling positions and IDs unchanged. The new rectangle plan commits
together with pane records after geometry validation and child resize success.

`smux_arrange_window(session_id, window_id, cols, rows)` projects the current
plan. Manual boundaries use floor(reference_boundary * target_size /
reference_size); right/bottom boundaries are projected independently of width
and height. Returning to the reference canvas restores exact coordinates.
Successful reflow changes the current canvas but retains reference boundaries.
Splits, explicit pane resizing and closes re-anchor the plan at the current
canvas. Named selection intentionally replaces manual geometry.

Every rectangle must have a positive area, lie within the bounded canvas, have
a unique pane ID and not overlap siblings. A resize that collapses any pane is
refused before any child resize or service-state write. Separators and holes
scale with boundaries; a separator can become zero-width under rounding while
panes remain disjoint. This is rectangle scaling, not a new minimum-separator
policy. Closing leaves surviving rectangles in place, with no implicit grow.
An empty window publishes no rectangles and refuses arrangement. A newly
created one-pane window projects its established full canvas.

Explicit multi-pane resizing preserves the pane origin and must fit within the
window without overlap. It can shrink a pane and leave unused space. Resizing
the sole pane changes its canvas and anchors it at the origin. The previous
unbounded multi-pane resize could place panes outside their window; the
updated contract deliberately refuses that invalid geometry.

All-window reflow and named selection share the existing child resize owner,
which validates all pane mappings before sending resize calls and attempts to
roll back earlier children on failure. Service metadata commits once only after
success; rollback failure remains an explicit error. Single-pane split/resize
retains the existing provider path. No claim of OS-level atomicity is made.

Interactive frame reflow and `client-layout ... current` use the current-plan
API rather than selecting tiled. Window activation copies manual state intact;
attachments still constrain the session canvas by their minimum dimensions.
Cross-session/window validation remains in the authoritative API. Session
identity resolution uses the root-owned shared resolver.

Failed child creation uses `smux_rollback_split(session_id, window_id,
added_pane_id)`. The API retains one private checkpoint per live window, bounded
by the existing eight-window capacity. A successful split records the original
window reference plan, pre-split rectangles and expected post-split geometry and
child handles. Reset clears checkpoints; a new split replaces that window's
checkpoint. Callers never supply replacement service state.

Rollback refuses changed pane IDs, sizes, child PID/PTY handles, window name or
geometry, and refuses a new pane with a child. It resizes prior children through
the existing transaction owner before restoring the exact prior window reference
plan and removing the childless new pane. Current pane output, input, focus and
window activation survive; consumed pane IDs are not rewound. A checkpoint is
consumed on success. A failed rollback remains explicitly reported by both
interactive and remote split paths. The ordinary close API is deliberately not
used: close-plus-resize would re-anchor rounded 40-column coordinates and turn
an original 39-column pane into 38 columns on returning to an 80-column canvas.

Acceptance evidence is authored in `smux_service_layouts_spec.spl` (nested
shrink/grow restoration and refusal atomicity), `smux_service_features_spec.spl`
(valid targeted resize), `smux_protocol_features_spec.spl` (manual publication)
and the sibling-owned `smux_major_features_phase3_spec.spl` (decoded split
commands, repeated frames, attachment/window/session isolation). Existing named
layout and provider rollback suites remain required. Runtime status is BLOCKED
until a genuine Phase 3 producer is supplied and admitted.

The service-layout suite also calls the exact rollback API used after failed
spawn, without allocating a child: 80-reference to 40-current, split, rollback,
then 80 restores every original boundary. A later named-layout mutation makes
the old checkpoint refuse. These are authored pure-layout transaction checks,
not injected provider failure or live-child rollback evidence.
