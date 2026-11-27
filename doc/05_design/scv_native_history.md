# Native history detail design

`ScvHistoryRevision` carries commit ID, stable change ID, ordered parents,
tree ID, and commit state. `ScvHistoryLimits` supplies maximum commits, parent
edges, and decoded commit bytes. Public `scv_history_walk` returns either the
complete ordered revision array or an error. `scv_log_all_parents` and
`scv_change_log` render that result through the existing CLI result protocol.

Enter frames validate/load a commit, charge budgets, append one revision,
and schedule a leave frame followed by parents. Leave frames clear active
membership. A repeated active ID fails; a completed visited ID is skipped.
The loop uses no recursive call stack. Malformed/duplicate required commit
fields and unsafe references fail before following parent paths. Change
records accept absent state for v1 compatibility and require open/closed for
an explicit state. Latest must belong to the selected logical change.

Requirements and executable acceptance:

| Requirement | Acceptance |
|---|---|
| REQ-SCV-HISTORY-001 | Both merge parents appear exactly once in deterministic stored-parent DFS; default log remains compatible |
| REQ-SCV-HISTORY-002 | Stable snapshot ChangeId, closed selected change and distinct new change, latest outside current ancestry, v1 open state |
| REQ-SCV-HISTORY-003 | Missing/invalid refs, cycle, nonregular object, duplicate field, latest mismatch, resource budgets, and wrong CLI arity fail explicitly |

Integration assertions cover graph and metadata contracts. System scenarios
exercise the real CLI for a conflicting merge and change lifecycle, with
bounded child processes and an explicit admitted-runtime selection. Runtime
execution, branch coverage, performance measurements, docgen, and
`sspec-maintain` remain NOT_RUN until that runtime exists.
