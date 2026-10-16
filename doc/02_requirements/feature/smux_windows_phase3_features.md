# SMUX Windows core-feature acceptance

These criteria come directly from the user's selected scope: native current
Windows, release_phase3, Phase 2 then Phase 3 compilation, tmux-like session
separation, windows, pane splits, background work, layout changes and multiple
screens. This is not a selection of new optional requirements.

| Requirement | Required behavior | Evidence owner |
|---|---|---|
| REQ-SMUX-CORE-001 | Independent sessions/windows, authoritative focus and ownership validation | Production service specs |
| REQ-SMUX-CORE-002 | Directional split geometry and atomic validation refusal | Production service specs |
| REQ-SMUX-CORE-003 | Addressed resize/focus, refusal without unintended mutation | Production service specs and live resize gate |
| REQ-SMUX-CORE-004 | Validated client attachment, capacity, rebind and scoped detach | Service and external client specs |
| REQ-SMUX-CORE-005 | Production service persists selected layouts and canvas, exposes real pane rectangles, validates ownership and invalidates stale geometry | Service layout specs |
| REQ-SMUX-WIN-001 | Real Windows ConPTY children, output isolation, retained state after detach | Windows child and external owner specs |
| REQ-SMUX-WIN-002 | Detached output beyond pipe capacity completes without capture/request polling | External owner-process specs |
| REQ-SMUX-WIN-003 | Sessions, shell panes and windows retain isolated state across disposable client processes | External owner-process specs |
| REQ-SMUX-WIN-004 | Wrong-token clients cannot mutate or stop the owner | External owner-process specs |
| REQ-SMUX-WIN-005 | Layout resizing reaches a real child's terminal dimensions | External owner child-computed Console dimensions |
| REQ-SMUX-INPUT-001 | Bounded byte queues retain partial writes, reject capacity overflow, surface deferred failures and keep other panes progressing | Input queue unit and external-owner backpressure specs |
| REQ-SMUX-INPUT-002 | Portable text-only PTY writes submit complete UTF-8 prefixes; native byte writes retain arbitrary partial-byte offsets | Portable codec unit and native ConPTY fixture |
| REQ-SMUX-HISTORY-001 | Bounded retained terminal cell rows preserve Unicode and enforce configured history limits | Scrollback production VT specs |
| REQ-SMUX-HISTORY-002 | Only primary full-screen scrolling enters history; alternate screens and partial regions stay isolated | Scrollback production VT specs |
| REQ-SMUX-HISTORY-003 | Synchronized capture, erase, reset and resize preserve the documented history lifecycle | Scrollback production VT specs |
| REQ-SMUX-HISTORY-004 | History capture validates pane ownership and commits one coherent snapshot | Production service history specs |
| REQ-SMUX-HISTORY-005 | Remote history reads the focused pane with validated bounded line counts | Remote history and external-owner specs |
| REQ-SMUX-WINDOWS-NATIVE-PROVIDER-SELECTION | Ordered source roots select real native Windows TCP and ConPTY owners through stable app imports | Resolver specs, selected-source fixture and actual product build |
| REQ-SMUX-WIN-006 | A pane refusing input cannot block another session's commands or output | External-owner saturation/fairness scenario with outer watchdog |
| REQ-SMUX-WIN-007 | Child-generated lines beyond the visible screen remain retrievable through bounded history | External-owner real scrollback scenario |
| REQ-SMUX-INTERACTIVE-001 | Stateful Ctrl-B commands preserve exact ordinary input and prefix state across reads | Pure client input specs and actual interactive fixture |
| REQ-SMUX-INTERACTIVE-002 | Raw control/Unicode input reaches the explicitly addressed child without command newline insertion | Hex codec/protocol and actual terminal child output |
| REQ-SMUX-INTERACTIVE-003 | Independent terminal clients retain local window/pane selection without changing another client's view | Explicit-target service specs and two-client native fixture |
| REQ-SMUX-INTERACTIVE-004 | Render real synchronized styled cells and the selected pane cursor at the correct canvas positions | Frame snapshot specs and native terminal captures |
| REQ-SMUX-INTERACTIVE-005 | Browse retained history in a local copy viewport while protecting child input | Viewport specs and actual terminal interaction |
| REQ-SMUX-INTERACTIVE-006 | Save and restore both native console modes; detach closes only the client and leaves the owner and sibling client running | Native console fixture and supervised two-client fixture |
| REQ-SMUX-LAYOUT-001 | Five named layouts, persisted selection, correct rectangles and window isolation | Model and service layout specs |
| REQ-SMUX-LAYOUT-002 | Model selection survives focus, feed, zoom, resize and pane changes when it fits | Model layout specs |
| REQ-SMUX-LAYOUT-003 | Model compositing places row/tiled content at the selected rectangles | Model layout specs |
| REQ-SMUX-LAYOUT-004 | Real child output appears under each selected named layout | External owner-process specs |
| REQ-SMUX-PROTOCOL-001 | Authenticated bounded requests, correct active resources and scoped commands | Protocol and external owner specs |
| REQ-SMUX-PROTOCOL-002 | Exact byte-framed responses; truncated/extra data must fail | Protocol codec and external owner specs |
| REQ-SMUX-PROTOCOL-003 | User-facing layout, rectangles and composite screen commands use real service state | Protocol and external owner specs |
| REQ-SMUX-PROTOCOL-004 | Disposable request clients report command failure as a nonzero exit | Reply status and external owner specs |
| REQ-SMUX-OWNER-001 | Independent owner survives request-client exit and drains unattended output | External owner-process specs |
| REQ-SMUX-BUILD-001 | Compile and execute using matching admitted Phase 2 and then Phase 3 Windows producers | Exact-build reports and artifacts |
| REQ-SMUX-WINDOWS-PTY-SPAWN-OWNER | A resolved synchronous PTY spawn remains an ordinary call; real actor/task transfers retain their checks | MIR regression and actual imported-call fixture |

Named layouts are `even-horizontal`, `even-vertical`, `main-horizontal`,
`main-vertical`, and `tiled`. Split direction API aliases retain the existing
convention and are not tmux flag compatibility.

Full major-feature acceptance additionally requires independently rendered
terminal clients, live child terminal-size delivery, scrollback/copy behavior,
and explicit key-binding/input interaction coverage. Current tests and source
do not establish those gates. They cannot be removed from the user's scope to
declare this task complete.

Execution, generated manuals and traceability are tracked in
`doc/03_plan/sys_test/smux_windows_phase3_features.md`; all source-only results
remain unverified until the matching runnable artifact and assertions exist.
