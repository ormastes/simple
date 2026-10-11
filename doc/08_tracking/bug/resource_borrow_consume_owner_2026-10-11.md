# Resource borrow versus consume check: provisional owner repair

Base release: `a4ca8226e21f8df3374c3eea1109e6365c4d7d79`. PR3053 owns the original consumer import; this
change leaves the original pinning spec byte-for-byte unchanged.

## Cause and scope

`BorrowChecker.check_function` records all MIR facts before `NLLChecker.check`
propagates borrows. `record_move` checks only prior moves. The propagated
borrow set was never compared with the consume facts at its program point.
The original pending `Ref(l1, l0)` followed by `Drop(l0)` therefore passed.

The owner now checks consumes after propagation, at statements and terminators.
Direct reference identity follows Copy/Move aliases. A proven single-block
scan records the last direct reference use, including synchronous call operands.
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
