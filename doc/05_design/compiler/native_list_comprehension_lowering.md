# Native list-comprehension lowering

## Bug and selected requirements

Rust native HIR omitted `Expr::ListComprehension`; lenient mode returned Nil/ANY
without lowering its projection. `render_version_manifest` consequently emitted
an empty projections section. The selected fix is compiler support for the
existing expression syntax, not rewriting application comprehensions as loops.
Requirements and cross-agent ownership are frozen in
`doc/03_plan/agent_tasks/native_list_comprehension_2026-09-23.md`.

## Rust implementation

The dedicated HIR helper emits only existing IR nodes:

1. Evaluate/lower the iterable in the enclosing scope and derive its element
   type from an array, text, or integer range. Dynamic ANY follows the existing
   generic runtime loop boundary; known unsupported static types fail closed.
2. Allocate a generator slot and bind identifier/wildcard/tuple patterns in a
   fresh lexical scope. The scope saves both local-slot and nominal type-hint
   bindings. Tuple patterns extract fields from the single generator slot.
3. Lower the filter, then projection. Infer the result array's element from the
   projection, including function-valued projections, rather than its input.
4. Emit a Block containing a fresh empty result array, a For loop with optional
   If around a typed `push`, and the result local as the block value.
5. Restore the saved name/hint bindings on success and error. Allocated slots
   remain stable because generated expressions refer to indices, not names.

No new HIR/MIR wire variant or runtime ABI is added. Existing loop lowering owns
iteration/decode; existing typed array append owns result boxing. Evaluation is
fused: one iterable evaluation per generator entry, one filter per item, and one
projection/append per accepted item. Complexity is O(input + result) time and
O(result) runtime storage. No per-item environment snapshots are introduced.

Known homogeneous tuple iterables are rejected: existing MIR For does not
unbox their scalar values consistently with HIR inference. This is distinct
from supported tuple patterns over array elements. Noninteger range bounds
also fail before integer-counter MIR lowering. Unsupported patterns fail even
in lenient mode. The unrelated lenient fallback for other AST forms is unchanged.

## Pure-Simple and evidence boundary

The pure-Simple owner implements its existing ordered Comprehension node through
HIR scope/type propagation, type inference, and a fused MIR traversal. That is
a separate owned diff, reviewed and tested independently before integration.

Rust interpreter currently batches filters before projections. That separate
ordering defect is tracked in
`doc/08_tracking/bug/list_comprehension_interpreter_filter_order_2026-09-23.md`;
this change does not claim interpreter side-effect parity.

Rust unit tests inspect real HIR structure, type propagation, error diagnostics,
and scope restoration. Native fixtures assert exact stdout and exit status for
general semantics and the production manifest round trip. Verification uses a
private clone of the admitted Rust authority's Cargo target with a one-job,
5,859,375 KiB sampled-tree cap. No full CLI/bootstrap build is authorized.
Artifact/source hashes, cache activity, elapsed time, RSS and watchdog cleanup
must be recorded before acceptance. Broader compiler/MCP/LSP and Phase2 gates
remain the parent lane's responsibility; no such PASS is inferred here.
