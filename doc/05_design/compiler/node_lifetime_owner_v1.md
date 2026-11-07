# AST expression lifetime owner

Status: implemented, source review approved; runtime qualification pending.
This is one W2 consumer slice of [node attributes](node_attributes.md), covering
REQ-004 and the checked binary-expression write portion of REQ-005. It does not
complete the construction obligation in REQ-003 or admit ready-node removal.

`compiler.frontend.node_lifetime_v1` is the sole checked reference boundary for
the expression arena. `AstExprHandleV1` binds the exact owner, active store
incarnation, and expression index. Every checked operation compares the current
authority and bounds before projecting storage. Binary operations additionally
check the owner's internal expression family; no public type tag is required.
The conversion from a raw expression index is an explicit legacy boundary and
only qualifies an index in the currently active arena.

The expression arena owns the incarnation cell. It is process-local and omitted
from snapshots, cached pool bytes, diagnostic generations, and store records.
Direct reset, store take/install, and cache restore invalidate references before
the first mutation. Reinstalling the same snapshot requires fresh handles.
Incarnation exhaustion permanently retires checked access instead of wrapping.
Legacy raw AST readers and constructors retain their existing interfaces.

The stable storage-adapter key is the exact owner/incarnation/index text after
validation. Sparse and reference adapters must request validation on every
operation; comparing two stale cached keys cannot establish current lifetime.
This identity is not a serialization or cross-process transfer capability.

Checked scalar setters write the canonical arena and compatibility mirror.
Checked child setters validate both references, then traverse the canonical
`ast_traversal` expression, statement, and match-arm projections using a tagged
worklist and a shared visited dictionary. Reachability of the parent rejects the
candidate edge before any write. Valid newer children remain legal; slot order
does not determine topology. A bounded worklist reports resource exhaustion
explicitly. Neither a rejection nor an exhausted traversal changes the parent
or its neighbors. Reads use constant-size qualification checks; cycle traversal
occurs only on child writes and costs O(V + E) within its declared budget.

W3 owns generated views and reference adapters and delegates their live binding
to this owner. It must not introduce a second ready-handle lifetime registry.
The forthcoming construction owner separately tracks pending obligations; those
tokens are not ready AST identities and cannot replace lifetime validation.

`test/01_unit/compiler/frontend/node_lifetime_v1_spec.spl` checks actual arena
values, neighboring nodes, self and indirect cycles through expression/statement/
arm domains and inline assembly inputs/outputs, accepted newer children, invalid owners/families/bounds, reset and
slot reuse, store switching, successful and failed restore, bounded traversal,
and non-wrapping incarnation progression. Execution remains unperformed while
the admitted runtime is unavailable; source checks are not runtime evidence.
