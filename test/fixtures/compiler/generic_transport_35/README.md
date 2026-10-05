# Original Phase 3 generic type transport

Status: native **UNRUN**. Source assertions are not execution evidence.

`sites.json` maps all 35 original explicit calls at revision
`96eaa4da8783f56a3a7954399fbb83573e36afa4`: 34 CAS calls (7 transaction,
7 unit, 18 text, 2 integer success types), plus `walk_hir_expr<MatchSiteScan>`.
The two `original-*.txt` files preserve the complete original source bytes;
their SHA-256 values are recorded per site. They are parser inputs, not build
entries and not replacement production modules.

Build `main.spl` with the candidate compiler sources included in its closure.
Running the resulting binary from that candidate's root executes its linked
parser, HIR lowering, monomorphizer, flat snapshot codec, and enum-contract
callback. Merely compiling this binary with an old compiler is not a test PASS.

Expected: `generic transport: 77 checks, 0 failures`, exit 0, and 70 unique
site/phase PASS records plus the callback and six parser-neighbor PASS records.
Neighbors cover shift, triple generic closings, comparisons, implicit calls,
ordered array arguments, and semantic-hash invalidation. Every original source line is
matched exactly once in cold and warm phases. Warm restore follows an unrelated
parse and must not increase the parse counter. Inventory, missing snapshot,
duplicate call, lost type, unresolved specialization, and callback failures
produce nonzero exits. Early infrastructure failure means later checks UNRUN.

The isolated HIR calls retain the exact parsed callee/type syntax but omit
runtime arguments, preventing inference from hiding explicit-argument loss.
This tests all original **transport sites**, not 34 filesystem fault paths.
The final acceptance gate remains the original unchanged Phase 3 workload;
neither this manifest nor representative tests retire its workaround.

Build `schema_main.spl` separately. Set `SIMPLE_GENERIC_GENERATED_OUTPUT` to an
absolute private owner output directory. It invokes the real schema emitter,
writes both generated candidates there, and checks their exact bytes against
the checked-in files. Expected: 4 checks, 0 failures. A parity failure preserves
generated artifacts for review; never copy them into a running source snapshot.
The initial candidate has stale registry headers, so parity is pending repair.

Execution needs canonical owner admission, a 20-job reservation under the shared
80-job ceiling, pinned producer/source/entry hashes, private outputs, and closed
compile/run RSS receipts. Run both backends; record actual counts, exits, elapsed
time and peak tree RSS independently. No seed, no guard bypass, no restart of
active builds. Parser neighbor cases are in
`test/01_unit/compiler/frontend/explicit_call_type_transport_spec.spl`.
