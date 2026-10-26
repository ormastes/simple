# Caret multiplexer and optional TUI interface: local research

2026-10-25. Baseline release/1.0.0 `1e431722b40`; subsequent unqualified source fixes are separate. The user selected option A and NFR profile N2; final requirements are under doc/02_requirements/{feature,nfr}/caret_mux_tui.md.

## Existing owners and caller contracts

The complete caller audit is [Caret compatibility matrix](../../09_report/caret_smux_compatibility_2026-10-25.md). Real dashboard host operations live in `src/app/llm_caret/pane_backend.spl`; independent workspaces in `agent_workspace.spl` use private tmux servers. Several swarm classes merely record commands and fabricate pane IDs: these must become real adapter calls before claiming usable replacement. The in-process smux dashboard loses its service state when the dashboard exits. Independent smux server ownership is implemented elsewhere and needs connecting to Caret's lifetime contract.

Caret needs real pane IDs/PIDs, exact target selection, literal input distinct from named keys and paste, styled/history capture, zoom/restore, layout/resize, process lifetime, cwd/argv preservation, isolated workspace cleanup and namespaced servers. A CLI executable rename cannot satisfy its format and status parsing. Common API migration and tmux-argv compatibility are distinct deliverables; preserve both where actual existing callers require them.

`src/os/apps/smux` owns terminal service state and geometry. The current worktree adds persistent manual rectangles and recipient-scoped notifications, but these are authored and unexecuted. Independent review identified failed-spawn geometry rollback drift; a freshness-checked split checkpoint correction now restores the original reference canvas and has passed source rereview. No successful compilation or full feature claim follows from source changes.

## Fit with the Simple UI stack

`doc/04_architecture/ui/shared_ui_contract.md` already defines backend-neutral widget/event semantics, with separate protocol contracts. `ui/testing/typed_ui_interface_arch.md` owns UI identity and test access, not pane process lifecycle or rendering. Reuse these for Caret content inside a pane. A multiplexer extension should own terminal-cell rectangles, focus, overlays and input routing only; it must not create another widget tree, GUI/window manager or competing UI test protocol.

Recommended composition is a shared mux session/pane interface plus optional terminal layout and optional terminal presentation capabilities. Keep a future general UI integration in the established UI layer. Caret can run its existing TUI as a normal pane child under either backend even if richer host-owned presentation is unavailable.

Required Caret focus, zoom/restore, resizing and layout operations belong to the mandatory mux interface. Only stronger complete-plan/revisioned transactions beyond those caller contracts are optional layout capabilities. Required titles, borders, hide/show, rebalance and notification delivery likewise cannot be reclassified as optional just because they affect presentation. Independent Astra review identified and corrected this scope distinction.

## Failure contract proposal

Every backend answers core session/window/pane operations with typed results. Optional capability acquisition is separate. A capability descriptor reports support level, limits, backend/version/owner generation, constraints and evidence status. Advertised support and actual execution qualification are different facts.

- `Unsupported`: valid operation absent from this backend/version; no mutation.
- `InvalidRequest` or `InvalidTarget`: malformed arguments or missing/wrongly owned handle.
- `PermissionDenied`: identity or policy refusal, never a fallback trigger.
- `Unavailable`: supported operation currently unusable because backend/transport/host is down.
- `StaleRevision`, `Busy`, `Timeout`: distinct retry policies; query before retrying an operation whose commit is uncertain.
- `PartialFailure`: retain successful changes, pending cleanup and actual state/revision; never report atomic success.

Layout input includes an expected revision and a complete validated cell plan. Validate before changing any child. Tmux may lack an equivalent multi-operation transaction: report that limitation, expose serial observed results or refuse the stronger operation. A capability probe does not guarantee the next operation succeeds.

Do not silently switch the selected backend: existing process IDs, socket authority, sessions and input could otherwise change owners. An exact semantic software implementation can be declared Emulated with constraints; clipping or a different layout is not equivalence. Required Caret compatibility gaps stay failing/blocked; only genuinely optional UI controls may be disabled with an explanation.

## Tests needed

Run the same core contract suite against smux and actual tmux; assert native effects, result/error semantics and no mutation on unsupported/invalid requests. Add provider-specific optional suites, resize/zoom restoration, nested splits, concurrent client resize, stale handles, exact Unicode cells, alternate-screen/input routing, backpressure and disconnect recovery. Retain Caret end-to-end workflows and exact legacy command-format tests. Phase3 compiler and native suite qualification remain blocked; no source-only test count is execution evidence.
