# Database optional receiver and ordered prefix

Checkpoint74 groupD; authored real-owner regressions, runtime/typecheck/native
qualification **UNRUN**. Test source is the matching unit SSpec under `test/`.

1. Import the actual async database facade, which reexports the sync table
   owner. Create real rows, unwrap `get_table_mut` with `?` into an unannotated
   binding, update a row and soft-delete another, and explicitly write the
   table back to its database. Save to a fresh temporary SDN file, reload and
   require the exact values and deletion flags. Missing tables return absence;
   invalid row keys return false. The row count and unaffected values remain
   intact. This does not replace table methods with local mocks or stubs.
2. Query actual inserted rows with limits zero, one, shorter, equal, longer
   than the table and negative. Require exact ordered prefixes before and
   after sorting, filtered descending order and a valid empty result. Mutate
   a returned copied row and confirm the source table and repeated query stay
   unchanged. Negative limits retain the existing array method's clamp-to-zero
   contract; no negative array index or slice behavior is substituted.

The separate native negative fixture has an actual `main` invoking
`wrong_receiver_v1`, which calls `mark_deleted` on a scalar after `?`. The
qualified native runner must select that entrypoint and a fresh output path.
The negative control passes only when compilation fails with the exact
`unresolved method call: mark_deleted` diagnostic associated with this
fixture's scalar receiver, and no object/executable output is admitted. A
nonzero status alone, a missing entrypoint, linker error, parse error, timeout,
or an unrelated diagnostic is **UNQUALIFIED**, never PASS. Record exit code,
diagnostic/source location, requested output path and the absent-artifact
check together. No command, diagnostic, or artifact check has run here.

A genuinely rebuilt producer is required to validate the compiler change.
Existing failed producer645 cannot establish its success. No build/retry is
launched here. `switch_operators_calls.spl` also has the independently approved
enum C4 patch `de831483`; operators must compose its distant hunk with this
packet's Try hunk against the pinned base and retain both. Never replace a
composed file with either packet's full after-image.
