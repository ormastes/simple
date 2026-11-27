# Pure CoreMux metadata queries

REQ-CMUX-002/004/005/007. **AUTHORED / NOT_RUN: 18 cases; zero executed.** This manual is source-authored, not generated or SSpec-qualified. The module calls production helpers over immutable DTO fixtures; it never launches or polls a process. Running/Exited fixture variants are data, not native evidence.

Shared steps/helpers are `metadata_setup` and `metadata_check_snapshot`. Expected values include concrete IDs, counts, revisions, rectangles, child states, optional references and errors; validation success alone is not the assertion oracle.

| Case | Expected result |
| --- | --- |
| Full namespace | Preserve order, revision 41, supplied child observations, limits and empty capability list |
| Hidden exclusion | Remove independent hidden p2, retain zoom-occluded p1, clear active/zoom/restore references and excluded layout/client references |
| Exited exclusion | Remove Exited p3; preserve Unknown and Running verbatim |
| Empty requested window | Retain w2 and ancestor s1, with no panes and pruned client pane reference |
| Session scope | Keep only s1's subtree and clients explicitly bound to s1 |
| Window scope | Keep w1 and s1, clear s1's out-of-scope current window; preserve coordinates and retained zoom/restore pair |
| Expected binding | Refuse wrong namespace, owner, generation or lease with NotApplied |
| Nil session context | Retain exact-window client despite optional nil session; do not invent its session context |
| Scope reference validity | Refuse foreign, stale and wrong-kind references |
| Absent scope | Return InvalidTarget, not a successful empty namespace |
| Hidden malformed input | Reject invalid ancestry before scope could conceal it |
| Input limits | Reject an over-limit input even if requested result would be smaller |
| Exact client context | Return its own window, rather than the session-global current window |
| Detached context | Bind only existing client identity; retain nil session/window/pane |
| Invalid client/binding | Refuse absent, stale, wrong-kind client and mismatched lease |
| Context graph | Refuse dangling pane or cross-session/window ancestry |
| Namespace collection growth | Retain all 12 exact ordered session/window/pane/client identities across ordinary array and map capacity growth |
| Layout collection growth | Retain all 12 pane references and original rectangle coordinates across ordinary array growth |

Filtering preserves required ancestors and prunes layout entries without moving remaining rectangles, reflowing windows, choosing focus, or inferring hidden state from zoom. The existing frozen graph validator is used before and after projection. Partial/empty capability descriptors are preserved as supplied metadata, never upgraded into mandatory provider support.

These cases do not authenticate leases, validate liveness of advertised PIDs, prove provider support, test capture/status/events effects, or establish network/system admission. Root owns the serialized Phase2 SSpec harness and actual runtime/profile receipts. Nothing here claims explicit-library-mode or Phase3 qualification.

Cycle 2 guards every projection append with exact length growth, and every membership-map insertion with length growth plus exact-key presence. A failed retention returns typed Unavailable rather than a complete-looking partial snapshot. Layout projection now propagates Result failures. The two added cases check ordinary successful growth and independently require complete fixture construction. They do **not** inject allocation failures or execute the error branches. All allocator-failure branches remain NOT_RUN; shared graph-validator allocation behavior is not qualified by these local checks.
