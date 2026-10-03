# Collection concat rewrite lacks ownership and liveness evidence

Status: source-review finding; runtime reproduction pending an admitted runner.
This blocks accepting the collection optimizer as fully verified under REQ-008.

`src/compiler/60.mir_opt/mir_opt/collection_opt_patterns.spl` matches an array
aggregate, a call spelled `+`, and a copy from the call result. Its
`colopt_match_copy_back` checks the source of that copy but does not require
the destination to equal the original array operand. The replacement emits
only a `push` call, dropping both temporary definitions and the copy.

Concrete MIR counterexample to preserve in a regression fixture:

1. `tmp = Aggregate(Array(i64), [7])`
2. `result = Call("+", [left, tmp])`
3. `other = Copy(result)`
4. Return or otherwise use `other`.

The current matcher accepts the first three instructions and replaces them
with `push(left, 7)`, leaving `other` without its required assignment. Even a
matching copy destination does not prove the removed temporaries are dead,
that `+` has canonical collection ownership, or that mutating `left` preserves
observable alias behavior. A later use of `tmp` is an additional counterexample.

Required repair: tests first for destination mismatch, live temporaries,
user-owned operator, and observable aliasing; preserve original instructions
unless typed call ownership, use/liveness and mutation legality are proven.
Record lost optimization opportunities explicitly if failing closed is needed.
Do not count an instruction-count change as executed semantic parity.

## 2026-10-03 conservative repair

The array three-instruction matcher now rejects every candidate because its
existing API has no ownership, liveness or alias proof inputs. Both production
entrypoints and direct matcher callers therefore preserve the original array
concat instructions. The string concat path and other transformations are not
changed by this repair.

This deliberately loses the previous concat-to-push allocation optimization:
repeated concatenation may retain quadratic copying/allocation. Restoring it
requires a typed operation authority and exact-region liveness/alias producer,
followed by semantic parity and performance evidence. No synthetic admission
flag or receipt can substitute for those facts.

Five authored regression scenarios in
`test/01_unit/compiler/mir_opt/collection_concat_legality_spec.spl` compare
complete production-pass blocks and terminators, cover both live temporaries,
copy destination mismatch, unproven operator ownership, aliases and the direct
helper. Runtime reproduction and full REQ-008 verification remain pending.
