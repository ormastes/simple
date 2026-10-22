# Ownership facts and loop backedges: required next implementation

Status: partial MIR/NLL implementation; not qualified across language routes.
This design addresses the remaining
`loops_without_false_positives` failure recovered from the saved seed lane.
Authority: no-GC ownership recovery plan §3.2–3.7 and WP-02. The same event
contract must cover pure-Simple HIR routes; seed-only acceptance is insufficient.

## Observed defect

`check_loop_moves` compares moved-at-body-end with moved-at-entry. It rejects
both a valid dominating refill before each move and a move followed by an
unconditional break. Removing that check would accept a repeated move.
Adding a blanket exception for a trailing break would also be unsound:
an earlier conditional `continue` can still reach another iteration.

The current branch accumulator also starts from moved-at-entry. It can
therefore retain a false moved fact even when every reachable branch revives
the place. These are control-flow problems, not requests for longer borrows.

## Event contract

During the existing typed traversal, produce one event stream with CFG edges.
Reuse type resolution, ownership sigil checking and place projection; do not
typecheck expressions repeatedly to approximate loop iterations.

- `ReadPlace(place)` reads that place and checks moved ancestors.
- `ReadWhole(place)` additionally checks moved descendants (partial moves).
- `Move(place)` requires a live owner and generates a moved fact.
- `Revive(place)` removes that place and descendant moved facts.
- `BorrowBegin(place, read|mutate, scope)` and `BorrowEnd(scope)` delimit
  call-local loans. Move/drop/conflicting mutation while loaned is rejected.
- `Call(effect_summary_identity, argument_places)` uses a checked contract.
  Missing contracts cannot infer a non-retaining call or implicit sharing.
- `Drop(place)` and cleanup edges consume the same live-owner facts. Drops
  are elaborated only after exactly-once cleanup can be qualified.

A place uses a scope-qualified binding identity plus field/index projections;
source spelling alone cannot distinguish shadowed owners. Type checking may
still fail immediately for kind mismatches, but path-dependent moved-use
errors must be decided on the CFG rather than rejected during event capture.

## CFG construction

Evaluate expressions in language order. Branch arms get separate successor
edges and only reachable predecessors contribute to a join. Preserve explicit
and implicit returns, including method tails; do not infer a move tail twice.

For a while loop, condition events belong to the header and execute on every
backedge. A for-loop iterable is evaluated once, while iteration bindings are
revived at each iteration. Fallthrough and `continue` target the loop header;
`break` targets its exit; `return` has no continuation in the current function.
Resolve labeled exits against the corresponding loop, not the nearest source
block. Nested-loop exits cannot be mistaken for outer-loop exits.

Use a worklist with maybe-moved sets, joining by union. Move generates facts;
revival kills facts. Transfer functions are monotone over finite place sets,
so each node/place input fact grows at most once. Check uses against incoming
facts after convergence. This avoids exponential path enumeration and repeated
AST/HIR inference. A fact/edge budget exhaustion is an explicit incomplete
error, never an unchecked success.

## Route and cache admission

Run the same pure-Simple fact checker before interpreter execution and native
lowering, including bootstrap routes. `--no-borrow-check`, an advisory profile,
or flat-bootstrap mode cannot disable strict ownership safety. Bind semantic
version, declaring-module strictness, imported contract identities and fact
schema to parser/HIR/object cache identity; regenerate affected codecs from
their authority. Unsupported ownership/runtime operations fail closed.

This pass does not make the current identity-only native `rt_unique_new`,
`rt_shared_new` or `rt_weak_upgrade` into real lifecycle implementations.
Exactly-once cleanup and weak liveness require separate WP-03 execution
evidence before no-GC runtime or Phase 3 readiness can be claimed.

## Required controls

Accept refill-before-move, per-iteration local ownership, disjoint branches,
revival on all continuing branches, and move-then-unconditional-break. Reject
move-before-refill, a moved while-condition operand, conditional continue that
reaches a second move, missing revival on a continuing branch, whole use after
partial move, shadowing-based resurrection and cross-suspension borrow escape.
Check state after loop exits as well as backedges. Exercise real seed,
pure-Simple interpreter and native routes and sabotage the backedge/read/kill
edges independently.

Implementation owner: this isolated Codex session. Sidecar implementation:
N/A. Independent design review: `nogc_hardening_review`; its read-only review
recommended this bounded ownership-event CFG. Final executable review remains
pending; this document is not verify PASS.

## Implementation mapping (2026-10-20)

`55.borrow/borrow_check/ownership_flow.spl` implements ordered Read/Move/Revive
events over the existing scope-identified MIR places. Incoming moved facts
are unioned over reachable edges and solved to convergence before diagnostics.
Definite writes kill covered descendants; symbolic-index writes do not prove
revival. The work budget and invalid/unmapped/duplicate point checks fail
closed. `nll.spl` captures these events during its existing recorder calls,
including reads at borrow creation and terminators; direct BorrowGraph users
retain their previous linear API. Native diagnostics and executable NLL unit
specs target this implementation boundary. The final solver source, including
alias isolation, and the NLL recorder integration fixture both passed their
native diagnostics in the user-authorized continuation. Block storage order
permutation preserves the diagnostic point. The std.spec file still requires
a qualified SPipe runner; full-language/source-route and lifecycle gates are
not established by these focused native checks. Exact hashes and logs are
recorded in the progress document.

Still required: typed-HIR event preservation and shared checking before every
execution route; short-loan start/end and call contracts; cleanup events and
drop elaboration; cache schema admission; seed loop parity; scope/labeled-exit
and full-language integration controls. Reaching convergence in the MIR
solver does not establish that preceding lowering preserves every source
ownership operation. The no-GC recovery plan and its remaining gates retain
their full scope.
