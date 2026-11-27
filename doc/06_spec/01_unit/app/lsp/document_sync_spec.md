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

11. Public didOpen/didChange/didClose handlers share the same document owner; Korean/emoji and CRLF survive exact snapshots, stale updates do not rewind, conflicting equal-version changes revoke trust, and identical close/reopen invalidates captured lifetimes.
12. Real collect_fixes_from_source produces an ordinary TODO-format action against a real temp file. The production-consumed completion seam accepts its source stamp, then refuses changed-source stamps and captured lifetimes after reopen. This is in-process completion integration, not child execution evidence.
13. External child execution is isolated in test/02_integration/app/lsp/revision_code_action_child_spec.spl. Ordinary unit scenarios do not require SIMPLE_BINARY. That integration requires an admitted runtime; no fake child or skip is supplied. All scenarios remain NOT_RUN.

R1 authority control: malformed full-sync changes at the accepted version revoke trust; older malformed events leave accepted authority intact. The actual public handler refuses actions until a newer valid full sync recovers ownership. NOT_RUN.

Malformed duplicate didOpen controls cover missing text at older/current versions and unknown version. Current/unknown observations revoke existing authority; strictly older malformed text does not. New full synchronization restores trust without resetting retained bytes.
