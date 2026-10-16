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
