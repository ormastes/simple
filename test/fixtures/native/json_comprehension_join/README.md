# Frozen-seed comprehension and join diagnostics

Bug: `seed_list_comprehension_join_and_empty_native_2026_10_21`.
These are bootstrap diagnostics for the frozen producer, not a claim that
comprehensions work or general compiler/suite qualification passed.

All cases import a real `Thread.join() -> i64?` declaration. The body asserts
that two mapped elements serialize to exactly `[1,2]`, including ordering.

| Case | Frozen seed build | Frozen seed execution |
|---|---|---|
| `original` | Fails optional `Add` in `main` | Not executed |
| `typed` | Succeeds | Fails, observing `[]` instead of `[1,2]` |
| `explicit` | Succeeds | Passes, observing `[1,2]` |

The additional private control renaming the unrelated `join` to `complete`
also compiled, but still observed `[]`; receiver typing and missing native
comprehension emission are separate defects. The unsupported-expression
lenient fallback in the seed emits `Nil/ANY` for `ListComprehension`.

After sourcing the admitted compiler toolchain environment, run
`sh test/01_unit/scripts/seed_list_comprehension_join_native_test.shs COMPILER TARGET RUNTIME_AUTHORITY FRESH_OUTPUT`.
It requires explicit producer/runtime paths, retains their hash and separate
fresh caches/logs/results for every case, and identifies both known failures
as expected failures. A changed producer that fixes either bug requires
reviewing these diagnostic expectations and the workaround retirement gate;
it must not silently normalize a newly passing original form back to failure.

The initial exact producer SHA-256 was
`32014B3401E3CB76AEC44ACB475A22F2385FEFCD1D19AB71049E52D633356825`.
Private exploratory evidence is retained under
`build/session/json-join-pollution/` in the isolated reviewer worktree.
