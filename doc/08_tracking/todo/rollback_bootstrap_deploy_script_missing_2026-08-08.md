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
