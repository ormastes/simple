# document sync spec

Status: authored operator outline, not generated execution evidence.
Generation and execution require the admitted pure-Simple runtime.

1. Open an empty document and inspect its integer revision.
2. Apply newer full changes; reject stale versions without rewinding content.
3. Reject a malformed later event atomically.
4. Retain final full replacement; prevent duplicate-open overwrite.
5. Reject unopened or malformed notifications.

See `doc/07_guide/tooling/lsp_revision_bound_code_actions.md` for authority and
remaining acceptance criteria. No public-protocol or release PASS is claimed.

6. Revoke synchronization after a malformed newer change; retain accepted bytes
   and version, refuse action queries, then restore only at the observed revision.
7. Fill the finite document and source-byte budgets, reject excess admission,
   and prove close/replacement reclaim the budget.

8. Reject a conflicting reopen at the same version and revoke stale authority.
9. Charge multibyte source/URI retention by actual bytes.
10. Grow an admitted source on disk beyond 1 MiB, call the real action handler,
    and verify it refuses before starting a child query; remove the fixture.
