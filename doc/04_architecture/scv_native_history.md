# Native history owner

The accepted implementation slice adds explicit all-parent log and logical
change inspection. It leaves existing log behavior intact and does not change
restore, commit publication, BuildRunner, or external VCS adapters.

`std.scv.history` owns checked loading, required-field admission, bounded
iterative traversal, and output construction. The SCV CLI parses argument
arity and translates the existing `ERROR` prefix into a nonzero exit code.
The reader uses the existing host file facade; no process or environment
access enters the history owner. Reference syntax is validated before object
path construction. Objects are not cached across requests, so no cache
invalidation protocol is needed.

Traversal keeps pending enter/leave frames, a visited map, and an active map.
Active membership is checked before visited membership, distinguishing a
cycle from an already completed shared ancestor. Parents are pushed in
reverse so stored parent order is preserved. Node, edge, and cumulative text
budgets bound both the result and pending frontier. Output is rendered only
after complete traversal succeeds. Work is proportional to admitted metadata,
nodes, and edges under the dictionary implementation's lookup behavior.

`change-log` captures the selected record's latest pointer, traverses from
that revision, validates that its ChangeId matches the selected record, and
filters rows by ChangeId. Workspace ancestry is irrelevant to an explicit
selection. This is an ancestry query rather than immutable rewrite evolution.

The owner performs bounded demand reads for each invocation. It adds no
startup scan, persistent index, background work, or external VCS dependency.
No startup/latency/RSS target is claimed without runtime measurements. Loose
storage, content-hash integrity, concurrent snapshot isolation, packed lookup,
and existing restore crash limitations remain explicit guide boundaries.
