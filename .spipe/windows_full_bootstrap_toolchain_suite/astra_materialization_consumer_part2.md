Changed:

- [authority.shs](C:/Users/ormas/dev/simple/scripts/check/lib/bootstrap-stage3/authority.shs): strict-v2 consumer, receipt environment wiring, native revalidation, directory-only exclusions, bounds, and atomic publication.
- [Focused test](C:/Users/ormas/dev/simple/test/02_integration/bootstrap_stage3_git_state_materialized_test.shs): synthetic positive and fail-closed fixtures.
- [Contract/report](C:/Users/ormas/dev/simple/doc/08_tracking/bug/windows_materialized_symlink_alias_git_state_timeout_2026-09-09.md): contract, exact test command, and outcome.

**Single test attempt: exit 1 during setup**, with MSYS `Permission denied` under `/c/Users/ormas`. Consumer assertions were not reached. Stopped without retrying.

Producer and unrelated edits were preserved. Implementation remains runtime-unverified; pending-creation races and real-checkout performance remain risks.