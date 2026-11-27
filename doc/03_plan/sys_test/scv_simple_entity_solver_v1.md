# Simple entity-edit solver validation plan

The selected scope is the source-only draft proposal slice from the SCV
solver gateway plan sections 6–8 (SCVN-S02). The implementation and manually
reviewed specification must preserve exact immutable inputs and require the
accepted policy's operation bundle before disjoint entity edits can combine.

| Criterion | Specification scenarios |
|---|---|
| Exact combined body edits and preserved inputs | Independent edits, invalid source, empty bytes |
| Revision-aware identity and complete source reconstruction | Same entity, stale bindings, unrecorded bytes |
| Verified file-move compatibility | Move plus edits, missing/stale moved-side evidence |
| Deterministic disjoint replay and conservative ordering | Reversed traversal, overlap, same-point insertion |
| Bounded host invocation and accepted policy | Operation tamper, duplicate IDs, count/budget/cancel |
| Independent validation cannot self-authorize | Ten checks, unavailable parse validator, unqualified draft |

Run the focused new SSpec and existing `scv_solver_host_v1_spec.spl` once with
an admitted pure-Simple release runtime. Then run required core/lib/MCP/LSP
checks and MCP stdio smoke because `src/lib` changed. Run SPipe docgen and
`sspec-maintain scan` on the focused spec/manual. Record exact runtime
identity and outcomes; native source checks, coverage and performance remain
not_run until that prerequisite exists.

Tests-first source commit: `ad4c1a215c1`. No admitted runtime is present in
this lane or the shared checkout; executable red/green evidence and every
runtime-dependent check are not_run. Static diff/ownership review and the
environment facade audit are separate evidence only.
