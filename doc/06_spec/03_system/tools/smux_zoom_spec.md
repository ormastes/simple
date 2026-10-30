# Smux window zoom and restore

Source: `test/03_system/tools/smux_zoom_spec.spl`.
Requirements: REQ-CMUX-004, 005, 008, 010.
Status: **WARN / NOT_RUN**. Sixteen scenarios authored; zero executed. This
mirror was written from the executable scenario bodies; admitted native docgen
and manual capture remain pending. No coverage percentage has been measured.

## What the user does

Caret's pane zoom action and the hosted interactive client's `Ctrl-b z` now
request the same authoritative window operation. A valid target expands to the
whole window. A second toggle restores the window even when another pane is
targeted. A one-pane window is unchanged. Background children remain owned and
can receive explicitly targeted commands while hidden.

The saved base layout survives attachment canvas changes. Explicit layout,
split, pane resize, different-pane focus and nonfinal pane removal restore the
base geometry before their successful commit. Selecting the already focused
pane preserves zoom. Closing the final pane deletes its window/session through
the existing checked lifetime path.

## Executable scenarios

| # | Scenario | Observation |
|---|---|---|
| 1 | Missing native resize capability | Pure production policy refuses owned PTYs; unbacked/piped grids remain valid. Synthetic handles never reach a provider. |
| 2 | Base and visible geometry | Base two-pane map retained, one full-canvas visible rectangle, target focused. |
| 3 | Different-target toggle | Already zoomed window restores instead of switching zoom target. |
| 4 | Single-pane toggle | No zoom state introduced. |
| 5 | Target identity | Foreign session/window and missing pane rejected without losing zoom. |
| 6 | Focus | Same pane preserves zoom; changed focus restores and selects the target. |
| 7 | Shared canvas | Shrink/grow reprojects from original reference; restored rectangles do not accumulate rounding. |
| 8 | Named layout | Explicit selection unzooms and survives subsequent toggles. |
| 9 | Split and checkpoint | Split uses base width; rollback restores prior zoom and all saved viewports, but refuses later independent focus drift or removal of a focused added pane. No native child in this control. |
| 10 | Refused edits | Invalid split direction and overlapping resize preserve prior snapshot. |
| 11 | Valid pane resize | Restore precedes new manual geometry. |
| 12 | Hidden-pane close | Pure removal unzooms; still-owned child cannot be removed. Typed uncertainty retains authority. |
| 13 | Window/session lifetime | Checked owner deletion removes zoom metadata; final-pane removal deletes final session. |
| 14 | Frame | Hidden content is absent while zoomed; hidden cursor rejected before capture; restore exposes sibling. |
| 15 | Interactive route | Prefix-z decoding, dispatcher, strict success-reply predicate, malformed/error rejection, invalid lease rejection, visible-only selection and hidden-input refusal. |
| 16 | Real Windows ConPTY | Child-measured viewport dimensions, hidden child commands, PID survival, checked teardown and pending-cleanup count. |

## Native observation procedure

Use a verified Phase 3 compiler/full CLI and its admitted runtime/provider tuple.
Configure the canonical SSpec command with explicit `--native-backend llvm`
and `--library-mode nogc-sync-mut`; keep broad canonical source roots. A physical
NoGC source directory is not the mode selector. The final argv must be bound by
the coordinator to that actual producer before running. No seed/interpreter
fallback, unguarded native process, or skipped ConPTY case can satisfy this gate.

1. Create an 80×24 window and vertical split; spawn two real `cmd.exe /d /q`
   ConPTY children. Each runs PowerShell to read its inherited
   `[Console]::WindowWidth` and `WindowHeight`: expect 39×24 and 40×24.
2. Zoom the first child: expect its measured viewport 80×24, the hidden child
   still answers at 40×24. Expected dimensions are absent from the sent command,
   so echoed input cannot satisfy the complete output marker.
3. Reflow the shared canvas to 100×30: expect the target 100×30 and both original
   PIDs present. Toggle using the other pane: expect restored 48×30 and 50×30,
   projected from the original manual reference, then obtain a real frame.
4. Attempt checked session teardown before any observation assertion. Require
   both original PIDs absent and PTY pending cleanup zero. Retain the external
   process-tree/Job quiescence receipt as well: numeric PID queries are not
   descendant-tree proof and remain subject to PID reuse/provider binding.

Provider refusal, delayed close, compensation failure, actual multiclient
console recovery and Caret's rendered UI still require real observations. The
pure controls above are not substitutes. Missing resize support fails closed
for owned PTYs. Incomplete resize compensation quarantines the window, retaining
all cleanup handles and permitting checked window/session deletion only.

## Difference on rejected edits

Smux retains its stronger preflight/rollback guarantee instead of imitating
tmux's incidental unzoom before a later split/layout error. Only a completed
compensation permits reuse of prior authoritative geometry. A native rollback
failure is an uncertain outcome, never a successful restore.

Source correction cycle 2 adds production reply-predicate assertions: successful
zoom and restore replies must remain successful through the hosted client's
response check, while errors and malformed resource IDs remain failures. A
split checkpoint also cannot restore zoom over a later focus decision or remove
an independently focused added pane, leaving the window without focused input.
These are additions within existing scenarios 9 and 15, not newly executed cases.
