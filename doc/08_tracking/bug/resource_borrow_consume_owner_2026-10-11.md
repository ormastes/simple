# Resource borrow versus consume check: provisional owner repair

Base release: `a4ca8226e21f8df3374c3eea1109e6365c4d7d79`. PR3053 owns the original consumer import; this
change leaves the original pinning spec byte-for-byte unchanged.

## Cause and scope

`BorrowChecker.check_function` records all MIR facts before `NLLChecker.check`
propagates borrows. `record_move` checks only prior moves. The propagated
borrow set was never compared with the consume facts at its program point.
The original pending `Ref(l1, l0)` followed by `Drop(l0)` therefore passed.

The owner now checks consumes after propagation, at statements and terminators.
Direct reference identity follows Copy/Move aliases. The current single-block
scan records the last direct reference use, including synchronous call operands;
block count does not prove an acyclic, straight-line lifetime (see the blocking
review below).
A previously used reference can cease preventing a later consume; a reference
with a future use or no recorded use remains pending. Returned aliases remain
pinned. Reference alias identities accumulate conservatively across overwrites.

Retirement is disabled for multi-block bodies, unknown/aggregate instructions,
and value-returning calls that could return an alias. Those bodies still receive
conservative borrow-versus-consume checks; validation is not silently skipped.
Void synchronous calls rely on the accepted call-scoped borrowing contract:
architecture resource declaration §8 invariant10 prohibits undeclared retention.
This patch does not prove that a callee obeys that contract.

## Diagnostic evidence

Immutable cached bootstrap producer SHA256:
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
The four actual current owners (lifetime, borrow_graph, nll, mod) are source-inline;
MIR and std.spec supporting imports remain unadmitted.

Cycle1: original unchanged assertion 0/1 PASS, 1 FAIL, peak114520KiB.
Cycle2: original assertion plus4 new call/direct-copy alias cases 5/5 PASS,
peak115672KiB. Cycle3: only2 fresh moved-alias/value-returning-call criteria
2/2 PASS, peak114740KiB. No green replay, rebuild or fourth cycle.
All collector jobs completed with final active process count0.
Exact fixture/log hashes and source bindings are retained in
`build/phase1-resource-pinning-owner-20261011/RESULTS.json` and
`{baseline,repaired,conservative}-binding.json`.

## OPEN production gates

This is not complete NLL retirement: existing borrow-conflict queries still see
logically expired borrow entries. CFG-sensitive lifetime/loop joins remain OPEN;
the conservative reverse check may reject legal multi-block callers. Aggregate
alias tracking and foreign retention declaration/verification are OPEN. The
original fixture contains neither a foreign call nor resource type metadata;
passing it does not demonstrate blocking/foreign-call duration safety.

Required admitted pure-runtime compiler/lib/MCP/LSP checks, integration and native
smokes, actual imported-owner qualification and representative CFG/caller
regressions remain OPEN. Keep this production PR draft; no historical backlog row
is qualified closed by cached bootstrap observations.

## Blocking independent review: single-block loops can retire live references

Review of source commit `db481c7d8ea` on PR3060 found that
`BorrowChecker.check_function` enables `reference_retirement_safe` using only
`func.blocks.len() == 1`. A sole block can terminate with a self-targeting
`Goto`, `If`, or `Switch`. `analyze_terminator` does not disable retirement for
these control-flow shapes. A reference use statically before a Drop can execute
again on the next iteration; `last_use < point` therefore does not prove that
its lifetime has ended. This is a blocking source correctness finding, without
a newly executed regression. The current implementation is not proven
straight-line and must not be admitted or merged.

Required repair: eligibility must establish an acyclic terminal body, rather
than count blocks alone. Conservatively disqualify control-flow/call/drop or
unknown terminators that can continue execution, and explicitly validate the
eligible terminal shape. Existing returned-alias escape checks must remain in
force. A future bounded feature cycle must cover a one-block back edge and
terminal eligibility before claiming safe retirement; callee retention and
other OPEN gates above remain separate requirements.

All three diagnostic cycles are exhausted. This checkpoint changes only this
tracking document; no source repair, new diagnostic, verification cycle, or
merge was performed. PR3060 remains draft.
