# Driver action-graph publication still takes a file lock

Status: open (follow-up from PR #6669, lockless SCV refresh).

`src/compiler/80.driver/action_graph/persisted_graph.spl`
(`persisted_graph_publish_v1`) takes `{root}/publication.lock` with a 5 s
timeout around a read-compare-rename of `{root}/CURRENT`, and answers
`publication-lock-unavailable` when it loses. The user directive of
2026-11-04 is that the compiler must be lockless; the SCV refresh,
inventory publication, snapshot retention and workaround index were converted
in PR #6669 (`doc/05_design/compiler/scv/lockless_refresh.md`). This is the
remaining sibling in the compile path found by that PR's review.

Shape of the fix (same pattern as the inventory pointer): generation files are
already written to a private `.tmp.<pid>` stage; publish them with
`file_publish_noreplace_raw`, drop the lock, and compare `CURRENT` against
`graph.parent_generation` immediately before the atomic rename, answering
`parent-generation-changed` (the existing reason) on a lost race so the owner
re-derives from the winner. Add the path to
`scripts/check/check-no-refresh-file-lock.shs` once converted.
