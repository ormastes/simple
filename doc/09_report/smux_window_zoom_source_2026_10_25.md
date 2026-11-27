# Authoritative smux zoom source candidate

Status: **WARN / NOT_RUN**, source correction cycle 2. Base commit
`7bc0826bf89d6f6b5a240468b1453435505f94a8`, isolated worktree
`D:/dev/simple-coremux-shared-20261025`. Original execution-worktree source and
its admission/materialization receipts were not changed.

## Problem and resulting behavior

Caret's smux `pane_zoom` previously toggled only `_smux_zoomed` in the dashboard
adapter. It did not resize a child, change the visible frame, or retain an
authoritative restore layout. That flag is removed. Caret now calls
`smux_toggle_zoom`; the interactive prefix-z action reaches `client-zoom`
through the existing authenticated lease-scoped request path.

The ordinary tiled-pane reference is tmux 3.5a's
[resize-pane implementation](https://github.com/tmux/tmux/blob/3.5a/cmd-resize-pane.c),
[select-pane implementation](https://github.com/tmux/tmux/blob/3.5a/cmd-select-pane.c),
[window resize implementation](https://github.com/tmux/tmux/blob/3.5a/resize.c),
and [server pane teardown](https://github.com/tmux/tmux/blob/3.5a/server-fn.c).
An already zoomed window always restores on `resize-pane -Z`, irrespective of
target. Same-active-pane selection is a no-op; selecting a different pane
restores. Window resize reflows the base and preserves zoom. Killing any
nonfinal ordinary pane unzooms. One-pane zoom is a no-op. Floating panes and
`select-pane -Z` are not introduced by this source slice.

## Owner and transaction design

`MuxWindow.zoom_pane` is an identity in the existing service snapshot. The
existing named/manual fields remain the base layout authority, including its
reference canvas. `window_base_rects`, `window_viewport_rects` and
`window_layout_rects` respectively project the restore map, all child viewport
dimensions, and visible rectangles. No second service global, copied live
owner registry, shared-contract mutation or runtime ABI was added.

Pure planning validates complete identity and geometry before effects. The
existing layout owner commits changed native viewport sizes through generic
`std.sosix.pty`. It compensates using the original snapshot, including the
failed attempt itself. Metadata and VT changes publish only after success.
`WindowGeometryUpdate.uncertain` carries incomplete compensation independently
of diagnostic text. API-owned closing-window quarantine then blocks further
input/layout/poll mutation and retains handles for checked owner deletion.
Owned PTYs without native resize support are refused before effects; piped and
unbacked grids may change without inventing a terminal capability.

Pane-close first releases the selected native owner using the existing checked
close path. Survivor geometry is restored before record removal. A resize
failure retains the released record, saved zoom/base map, pending intent and
all surviving handles. Incomplete compensation also installs closing-window
quarantine. Final-pane retry continues through checked window/session deletion.
Split checkpoints retain all actual pre-split viewports and zoom identity;
rollback cannot silently accept a changed zoom state.
If current focus has moved away from a saved zoom target, rollback refuses
before effects; it cannot overwrite independent focus or restore a hidden
active pane.
Rollback also refuses removing an independently focused added pane, including
an unzoomed checkpoint, so it cannot leave a surviving window without focus.

Interactive frames display only the zoomed pane. Interactive pane lists expose
only visible selection targets; input naming a hidden pane is refused before
enqueue. A stale hosted client reselects a visible pane and validates a new
frame without replaying the refused input or remaining actions in that chunk.
Explicit programmatic send-to-pane remains available for hidden children.
Caret pane metadata reads the service's zoom identity rather than a local flag.
The shared response predicate accepts exact restored replies or canonical
positive resource IDs for successful zoom, and rejects malformed/error replies.
This closes the reviewed path where the command applied zoom but the hosted
client incorrectly classified its response as failure and detached.

## Source scope and evidence limits

Eleven production owners: `src/os/apps/smux/{api,contract,window_layout_service,
pane_lifecycle,split_checkpoint,frame_snapshot,interactive_protocol,
interactive_client,client_input,smux_remote}.spl` and
`src/app/llm_caret/pane_backend.spl`. The focused executable spec and its manual
are `test/03_system/tools/smux_zoom_spec.spl` and
`doc/06_spec/03_system/tools/smux_zoom_spec.md`.

Sixteen scenarios are authored, zero executed. They include real ConPTY
child-measured viewport sizes and bounded checked teardown; they are not
passing counts. The pure capability/uncertainty controls never execute
synthetic handles and do not prove provider refusal or compensation behavior.
No compiler, helper, watchdog, test, server, console or product was launched.
Independent exact-source review, native SSpec/docgen/manual captures, child/Job
cleanup, actual client recovery and Caret UI qualification remain pending.
This candidate does not establish full tmux parity or release readiness.

Cycle 1's freeze is retained. Cycle 2 addresses independent review's reply
predicate P1 and focus-drift rollback P2, with production-path assertions added
inside the existing sixteen scenarios. No prior authored case is counted as a
native PASS, and no provider or compiler was executed during correction.
