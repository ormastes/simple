# Smux geometry and presentation source cycle 1

Status: **WARN / NOT_RUN**. Source implementation and authored scenarios only.
No compiler/build/test/helper/native/product launch, commit, worker restart or
release action occurred. Genuine Phase 3 execution remains unavailable. The
existing zoom scenarios remain unchanged and retain their prior NOT_RUN status.

## Owner state and interfaces

`MuxWindow.presentation: [MuxPanePresentation]` is the authoritative presentation
map inside ServiceState. Each entry contains `pane_id`, literal `title`,
`hidden`, typed `border` and typed `status`. There is at most one owner-created
entry per pane, with the existing service limit of eight entries. Titles are
bounded to 1024 UTF-8 bytes and reject C0/C1 controls before mutation. Valid
Unicode is stored literally. Rendering alone clips by terminal cell width.
There are no new MuxPane fields, native handles or secondary mutable registries.

Window constructors preserve entries. `with_geometry` prunes by the full set of
allocation IDs, protecting against stale-window replacement after pane deletion.
`without_pane_presentation(pane_id)` supports the separate ServiceState deletion
owner. Split checkpoints compare all presentation fields before restoring a
whole window and refuse later independent changes before native effects.

`pane_presentation_service` exports title/border/status, hide/show and rebalance
`*_plan` functions returning `Result<ServiceState,text>` and matching `*_state`
functions returning the existing `WindowGeometryUpdate`. The API owner publishes
success and applies its existing typed uncertainty quarantine policy. No string
parsing is used to decide incomplete-compensation state.

`window_layout_service.split_window_sized_plan/state` add typed MuxSplitSizeV1;
the existing `split_window_plan/state` signatures remain Equal wrappers.
`pane_presentation` exports `pane_presentation`, `pane_is_hidden`, and exact
`pane_presentations_equal` for API observation, interactive guards and revision
comparison. These sources use configured/generic std imports.

## Geometry and rendering policy

Stored base/layout rectangles are allocation boxes. Visible allocation excludes
explicit-hidden panes and respects window zoom. `window_content_rects` returns
visible content rectangles; `window_viewport_rects` returns all actual child
content rectangles, including background panes. Public CoreMux pane rectangles
and legacy API pane rectangles must use content dimensions.

Single and Double borders each reserve a one-cell perimeter. Top/Bottom status
reserve one additional row inside that perimeter, independently of border
visibility. Hidden border/status reserves no cells. Defaults preserve existing
borderless behavior. The frame renderer draws these glyphs and literal titles,
reads actual VT cells, and offsets the cursor by the same content projection.
Title cells and presentation entries are projected once per visible pane before
the bounded frame loop. The existing 512 by 256 / 60000-cell remote canvas and
65450-byte reply limits remain enforced.

Plans reject nonpositive content both in saved base geometry and zoom geometry.
Effects use the existing Sosix resize owner, compensate every attempted handle
on failure, and return its typed uncertainty if compensation fails. Pure state
updates do not publish before native success. No local platform FFI was added.

Cells refers to the new child content extent on the frozen split axis:
Horizontal is top/bottom, Vertical is left/right. One independent separator is
reserved; existing decoration costs are subtracted before computing available
content. The new child starts with Hidden border/status. Percent uses integer
floor of available content times percentage / 100; valid range is 1 through 99,
and both child content extents must remain positive. Equal assigns an odd
remainder to the new child, preserving the old undecorated Equal behavior.
Explicit resize requests are content dimensions and add decoration costs to the
stored allocation. Rebalance retains a selected named layout; Manual explicitly
selects even-horizontal. Hidden allocations remain included in layout edits.

## Visibility and lifecycle policy

Hide preserves allocation holes, native child ownership, output/history and
explicit-send authority. It rejects hiding the last explicit-visible pane.
Hiding a focused pane selects the first visible sibling; hiding the zoom target
restores base geometry. Hidden panes cannot become focus/zoom/split targets.
The API/interactive owner must reject stale interactive input while allowing
explicit targeted send. Frame capture also rejects an explicit-hidden cursor.

Show clears independent hidden state without stealing focus. An unrelated active
zoom remains in effect, so a shown sibling becomes displayed when zoom restores.
The explicit hidden flag is distinct from zoom occlusion. Closing the last
visible pane automatically reveals/focuses the first surviving background pane;
final-pane deletion remains the existing checked window/session teardown path.
Failed close or resize keeps existing handles and pending-close authority.

## Evidence and integration boundaries

Seventeen pure state/render scenarios and two real ConPTY scenarios are authored
with manual mirrors. The native oracles require real PID liveness, child-measured
dimensions, frame glyph/title presence, hidden output continuity, rejected stale
input, checked teardown and zero deferred cleanup. No successful fallback or
unavailable-provider skip is present. These have not been compiled or executed.

API/controller publication and dispatch are owned by the server author; capture
owns ServiceState pruning. Their files are intentionally outside this lane.
All mandatory operations remain mandatory; source availability is not provider
capability qualification. Runtime failure compensation, N2 performance/soak,
generated-manual review and complete provider operation admission remain pending.

Primary semantics reference: [OpenBSD tmux manual](https://man.openbsd.org/tmux)
documents new-pane size/percentage and border status off/top/bottom. CoreMux's
frozen axis names and explicitly accepted allocation/hide policies govern this
implementation; this source report does not claim pixel-identical tmux layout.
