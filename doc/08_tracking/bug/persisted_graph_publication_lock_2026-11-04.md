# Driver action-graph publication still takes a file lock

Status: fix-implemented-verification-pending (original lock removal and pointer retry source present; runtime qualification pending).

## Historical observation (2026-11-04)

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

## Resolution (2026-11-05, work/libbug-cas-graphpub-20261105)

Converted to the lockless inventory-pointer pattern
(doc/05_design/compiler/scv/lockless_refresh.md): the generation blob is
staged privately (`.tmp.<pid>`) and published with
`file_publish_noreplace_raw` (no-replace rename; identical-content race is
benign, same name with different bytes is `generation-conflict`). The
`{root}/publication.lock` `file_lock`/`file_unlock` pair and the
`publication-lock-unavailable` answer are removed. CURRENT is still replaced
by one atomic rename, but the compare-and-swap is a final re-read of CURRENT
against `graph.parent_generation` immediately before that rename: a moved
pointer naming our own generation returns `ok` (duplicate raced the whole
way), any other move returns the existing `parent-generation-changed` so the
owner re-derives from the winner. Nothing blocks; no lock file is ever
created. `src/compiler/80.driver/action_graph/persisted_graph.spl` was added
to the `check-no-refresh-file-lock.shs` scan scope. Evidence:
`test/01_unit/compiler/action_graph/persisted_graph_lockless_publish_spec.spl`
(no lock file, benign duplicate, superseded-base rejection, same-base race
loses with `parent-generation-changed`); regression
`persisted_graph_host_write_spec.spl` still green.

## Retry publication follow-up (2026-11-08)

Source review of release commit `e87258dba95a096fb1e2cf63e69651b101a11a15`
found that identical existing generation bytes returned `ok` before consulting
`CURRENT`. A failed pointer write can leave the generation blob behind, so a
retry could report success without publishing the pointer. Similarly, retrying
a graph rejected for a superseded parent could incorrectly return `ok`.

The candidate repair skips rewriting an identical immutable generation, then
continues through the existing pointer write and parent-generation check. It
does not change the concurrency algorithm or claim the read-then-rename is an
atomic compare-and-swap.

`persisted_graph_lockless_publish_spec.spl` adds two regressions: an existing
immutable blob with absent `CURRENT` must publish the pointer, and a second
attempt with the same superseded parent must still reject the publication.
Existing successful duplicate coverage remains in place.

Status: implementation and regression source prepared; execution pending.
No admitted full-CLI self-hosted runtime was available in this lane, so no
Simple test/check/build, interpreter/native qualification, or pass count is
claimed. Required verification includes the focused lockless publication and
host-write specs plus compiler/core/MCP checks under the repo verification
policy before closure or runtime qualification. The user authorized landing
reviewed source with these checks still pending. The original lock-removal
source was already present;
this follow-up does not newly claim that repair.

### Review context and additional regression coverage

At candidate base `e87258dba95a096fb1e2cf63e69651b101a11a15`, a tracked
`src`, `test`, and `scripts` symbol scan finds no production caller of
`persisted_graph_publish_v1`: the function is exported by its owner and used
by the two publication specs. Returning `parent-generation-changed` for an
older successful generation after a descendant becomes current is deliberate:
the operation publishes CURRENT, so historical blob existence cannot establish
that postcondition. A regression explicitly asserts the old replay rejects
without rewinding CURRENT. The stale-parent regression now also checks its
blob precondition and removal of CURRENT's staging file after each rejection.

The pre-existing absence of a generations-directory fsync after no-replace
publication is a separate crash-durability gap. This candidate leaves it
unchanged; its tracking follow-up is
`persisted_graph_generation_directory_fsync_gap_2026_11_08.md`.
