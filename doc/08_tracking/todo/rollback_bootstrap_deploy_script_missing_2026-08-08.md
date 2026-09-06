> **STATUS UPDATE 2026-09-06 — RESOLVED.** `scripts/bootstrap/rollback-bootstrap-deploy.shs`
> exists and is fail-closed. History note: it was actually first added on
> 2026-08-08 (`1a77c01e551`), the same day this TODO was filed; the tree-wipe
> incident at `6f86ff32a7d` (see `doc/08_tracking/bug/
> fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`) evidently made
> the file briefly disappear from a session's working tree, this TODO got
> filed against that transient state, and `ae55a746719` restored the file a
> few minutes later — but this doc was never revisited. On 2026-09-06 the
> script was additionally hardened to match the `scripts/check/*.shs`
> convention: `--selftest` (3 fatal fixtures, runs before every real
> invocation), `--dry-run`, a `PASS —`/`FAIL —`/`ERROR —` verdict line as the
> last line of stdout (a missing deploy receipt is now ERROR/exit 2, never a
> pass — previously it was FAIL/exit 1, conflating "no record" with
> "untrustworthy record"), a refusal (FAIL) when a rollback would leave
> `bin/simple` dangling, and a richer on-disk rollback receipt (`command`,
> `exit_status`, `pre_rollback_sha256`, `restored_sha256`, `smoke_output`).
> `test/03_system/check/bootstrap_deploy_rollback_contract_spec.spl`'s
> behavioral assertions (valid rollback, tampered-backup FAIL, invalid-platform
> ERROR) and all but two of its literal-text assertions on the script source
> still hold. **Still open, pre-existing, NOT part of this fix:** that spec
> also asserts the literal text `fail_receipt stale_current_tree` and
> `fail_receipt current_worktree`, which no version of this script in this
> branch's history has ever contained (traced to a divergent, never-merged
> branch, `a8244005f9b`, that added those checks under a different history
> line). That gap predates this fix and is left for a follow-up TODO rather
> than guessed at here.

# Bootstrap Gate 5R rollback script never built

`scripts/bootstrap/rollback-bootstrap-deploy.shs` is referenced as the
canonical Gate 5R rollback command by multiple docs/agents (`.claude/skills/
spipe.md`, `.claude/agents/spipe/dev.md`, `doc/07_guide/app/llm/
bootstrap_parallel_handoff.md`, `doc/03_plan/agent_tasks/stage4_spdev.md`),
but no file of that name (or an equivalent under a renamed path) exists
anywhere in the repo. `scripts/bootstrap/` has no rollback/deploy-restore
script at all today.

# TODO: [bootstrap][P2] Build `scripts/bootstrap/rollback-bootstrap-deploy.shs`
Implement the Gate 5R rollback script: given `<canonical-triple>`, restore
`bin/release/<canonical-triple>/simple` from the retained
`bin/release/<canonical-triple>/simple.pre_deploy`, verify the restored
SHA-256 against the pre-deploy hash, and re-run the arithmetic smoke
(`-c 'print(1+1)'`), printing a rollback receipt (command, exit status, path,
pre/post/restored hashes, smoke output). Until this lands, Gate 5R is
performed manually per the steps described in the docs above; the docs have
been softened to say "planned, not yet implemented" rather than presenting
the script as available.
