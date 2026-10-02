# Item 4 parallel ownership

Date: 2026-10-03. Initial inspection base and target at allocation:
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a` (`origin/release/1.0`).

Private lanes refreshed to `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c` before
integration. The intervening change affects the frontend flat-pool codec and
its two tests; inspected linker sources and the research document are unchanged.
Session metadata records this refreshed base/expected target. No runtime PASS
evidence exists to transfer across the rebase.

| Lane / owner | Isolated worktree and work branch | Exclusive edits |
|---|---|---|
| Integration / `/root` | `C:/dev/simple-item4-linker-dev-20261003`; `work/item4-linker-dev-20261003` | Plan/design, acceptance plan, lane ledger, subsequent reviewed production fix |
| Research / `/root/linker_research` | `C:/dev/simple-item4-linker-research-20261003`; `work/item4-linker-research-20261003` | Dated addendum to linker research |
| Acceptance / `/root/linker_acceptance` | `C:/dev/simple-item4-linker-acceptance-20261003`; `work/item4-linker-acceptance-20261003` | New item4 system acceptance spec |
| Runtime reconnaissance / `/root/linker_runtime` | Read-only existing environment; no work branch | No edits or interference with live bootstrap |

All coding agents use the inherited model; no lower-model sidecars are used.
Merge owner: `/root`. Final review owner: `/root` plus an independent same-model
agent after integration; reviewer must inspect the exact final diff and actual
RED/GREEN evidence. No reviewer is assigned to certify unexecuted tests.

Shared requirement IDs are ITEM4-REQ-001 through ITEM4-REQ-010 in
`doc/03_plan/sys_test/item4_linker_acceptance_2026-10-03.md`. Shared helpers are
`item4_load_elf_fixture`, `item4_static_link_error`, and
`item4_archive_with_member_type`; use canonical `std.spec.step`. Missing setup
or unsupported evidence must fail explicitly, never pass a placeholder.

Research commits are integrated before plan reconciliation; acceptance commits
precede production fixes. Each owner reports its exact commit and tests run.
Only owned commits enter the release-targeted integration branch. Existing
main-worktree dirty command files and other item1/item5/bootstrap worktrees
remain outside this change. Refresh the expected target before submission and
renew evidence affected by any rebase. Release refs move only through reviewed
PR integration; this task does not authorize release tags or publication.
