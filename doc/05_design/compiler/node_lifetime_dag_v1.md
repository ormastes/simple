# Complete DAG checks at existing AST edge writes

Status: implemented; runtime qualification pending. This is a scoped REQ-004/005
correctness repair, not admission of a cached parser construction feature.

The existing target-reachability check rejected a candidate that reached its
new parent, but accepted a candidate already containing an unrelated cycle.
For example, a raw binary node can point to itself. Installing that node as a
different parent's child passed the former visited-set traversal and preserved
the cycle. A raw binary with an unset required child could likewise pass.

`node_lifetime_dag_v1` walks the canonical expression, statement and match-arm
projections with domain-tagged gray/black DFS state. It checks actual arena
bounds before projection, validates an if statement's elif reference before
dereference, and rejects missing binary children and every existing cycle.
An optional forbidden expression folds parent reachability into the same walk.
The existing `node_lifetime_child_edge_error_v1` entry delegates to it.

Before mutation, checked left/right setters validate both the proposed child
and the unchanged sibling, forbidding either from reaching the parent. A bad
edge being replaced does not prevent a legitimate repair. Valid newer children
and shared acyclic subgraphs remain legal. Rejection preserves both fields and
allocates no AST node. Checked scalar reads/writes retain their prior behavior.

Validation retains no proof between operations and makes no assumption about
array copy-on-write conformance. In particular, the current frontend interpreter
can share arrays across bindings/returns through `val_copy_if_value_struct`
and mutate their shared value on indexed assignment. The new alias regression
uses the actual owner state as its structural oracle and checks safety on either
engine behavior; it does not certify array value semantics.

Each child write performs at most two O(V + E) graph walks, one per resulting
child graph, with explicit bounded work and a resource-error result before any
write. This is a correctness check on mutation, not a repeated whole-tree scan
on reads. No latency/RSS or runtime test result is claimed.

`node_lifetime_dag_v1_spec.spl` authors real-owner regressions for unrelated child
cycles, missing/future children, both unchanged sibling checks, accepted newer
shared children, repair, invalid elif metadata, changed graphs and taken arenas,
array-alias safety, and bounded traversal. These remain unexecuted while the
admitted self-hosted runtime is unavailable. Cached DAG proofs, whole-node
construction and production parser enablement remain held until meaningful
array-ABI capability integration and required metadata artifacts are admitted.
