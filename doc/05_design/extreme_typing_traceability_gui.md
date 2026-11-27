# Slop and Caret trace/API view sketch

Status: proposed extension of existing Slop, 2026-11-01. No capture or UI
execution claimed. Reuse `session.spl`, `view.spl`, `projection.spl` and
`native_frame.spl`; the common TraceViewProjection owns semantics.

```text
+ Snapshot [git:OID]  Agent overlay [none]  Freshness [local captured] +
| Groups / features | Requirements | Code | API | Bugs | Matrix      |
| Tree              | Graph / sparse matrix       | Inspector       |
| canonical IDs     | typed edges + precision      | reason path     |
| aliases select    | unknowns / truncation        | source + origin |
| same entity       | static / observed toggle     | evidence state  |
+ Focus / selected ID retained; stale data clearly labeled --------+
```

Separate matrix selectors choose feature-by-layer membership or directed
layer-by-layer dependency. Cell drilldown retains snapshot and filters; shared
symbols have one identity. API pane shows export closure and the first failing
leaf, then other paths. Inspector distinguishes definition linkage, observation
outcome and qualified evidence; "linked" is never green "passed".

Caret embeds this viewer with registered agent/session overlays. A comparison
chooses base/head/staged/dirty snapshots explicitly and shows added, removed,
changed and unresolved semantic facts. Overlay badges say "overlap"; a merge
conflict badge requires real conflict evidence. Detached/unavailable worktrees
remain visible. Actions do not start/stop agents or mutate worktrees.

Navigation supports keyboard focus, tree/graph/inspector selection, safe
historical source opening and cancelable refresh. Snapshot switch invalidates
cursors; failed parsing retains visibly stale last-valid view. Private material
is filtered before layout; source artifact visibility is distinct from
compiler publicness and caller authorization. PR metadata has freshness and an
explicit refresh action; offline browsing performs no automatic network call.

Planned screenshot/golden/diff evidence:
`doc/06_spec/image/03_system/app/traceability/feature/`. Generated manuals must
embed real captures only after executable scenarios run and receive review.
