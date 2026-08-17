# jj push bypasses rules.sdl gates (2026-08-11)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Mechanism

`.git/hooks/pre-push` (`scripts/check/pre-push-conflict-tree-guard.shs`) fans out to
~57 guards, including the rules.sdl shrink gates added by the P3 anti-fraud campaign
(`scripts/check/check-rules-sdl.shs`, `scripts/check/check-rules-sdl-integrity.shs`).
That hook only fires on a real `git push`.

This repo's documented VCS is jj (`.claude/rules/vcs.md`), and the standard landing
flow is:

```
sj bookmark set main -r @- && sj git push --bookmark main
```

`jj git push` does not invoke git hooks at all — jj has no pre-push hook mechanism.
`sj` (`bin/sj` -> `src/app/sj/main.spl`) is a thin, fully generic passthrough that
execs whatever jj/git subcommand it is given (`exec_args` in
`src/app/sj/client.spl`); it has no push-specific branch to hook into. Confirmed by
adversarial review 2026-08-11: on the standard landing path, the quick-group
rules.sdl gates never ran. The only real enforcement point before this fix was
`bin/simple build bootstrap` (full group, via `src/app/cli/bootstrap_check.spl`
check 9), and nobody runs bootstrap on every landing.

## Investigation

- `command -v sj` resolves to `/home/ormastes/dev/pub/simple/bin/sj`, a POSIX shell
  script that locates a working Simple runtime and execs
  `<runtime> run src/app/sj/main.spl "$@"`.
- `src/app/sj/main.spl` is a generic jj/git command forwarder (`sj_get_args` ->
  `exec_args`) with no awareness of `push`, `bookmark`, or any other specific
  subcommand — it is not a natural place to splice command-specific gating without
  parsing arbitrary jj/git argument vectors, which would be fragile and easy to
  route around (`sj raw jj git push ...`, `sj git push ...`, plain `jj git push`,
  etc. all reach the same git transport without going through any single
  recognizable "push" code path in this wrapper).

## Fix applied

Approach (b): a new gate-then-push wrapper, **not** an edit inside `sj`/jj
internals. Added `scripts/check/land.shs`:

1. Resolves `TIP` (`jj log -r '@-'`, falling back to `git rev-parse HEAD`) and
   `BASE` (`git rev-parse main@{origin}` / `origin/main`).
2. Runs `check-rules-sdl.shs --group quick --ref "$TIP"` and
   `check-rules-sdl-integrity.shs "$BASE" "$TIP"` against COMMITTED content.
3. Reads the LAST LINE of each guard's stdout (verdict discipline, matching the
   other pre-push guards) — refuses to push (exit 1) unless both verdicts start
   with `PASS`.
4. Only on a clean gate does it run `sj bookmark set main -r @- && sj git push
   --bookmark main` (falling back to plain `jj bookmark`/`jj git push` if `sj` is
   unavailable).
5. Supports `--dry-run` to run the gates without pushing.

Smoke-tested 2026-08-11 with `sh scripts/check/land.shs --dry-run`: correctly
resolved BASE/TIP, ran both guards, parsed the `check-rules-sdl.shs` FAIL verdict
(`rules_sdl_gates: 0 < min 12` — rules.sdl not yet committed at TIP, a separate,
already-tracked P3 Task C item) and refused to push. `sh -n scripts/check/land.shs`
is clean.

Docs updated to make this the documented landing command:
- `.claude/rules/vcs.md` — "Push:" line now points at `scripts/check/land.shs`
  instead of the raw `sj`/`jj git push` line, with an explicit warning against
  using the raw command.
- `doc/07_guide/infra/llm_fraud_prevention.md` — "Where enforcement actually
  happens" now lists `land.shs` as the primary enforcement point for the
  non-bootstrap landing path.

## Open residual risk

`land.shs` only protects sessions/users that actually invoke it. Nothing prevents
a user or agent from running raw `sj bookmark set ... && sj git push ...` or plain
`jj git push` directly — jj has no hook mechanism to force routing through the
wrapper, and `sj` itself was deliberately left as a generic passthrough rather than
modified to special-case `push` (a special-cased edit inside `sj` would be brittle:
any alternate spelling of the push command — `sj raw jj git push`, `sj git push
--bookmark main -r ...`, calling `jj`/`git` directly, bypasses jj/`sj` altogether —
would route around it the same way the current gap exists). This fix closes the gap
for anyone following the now-updated documented flow; it does not make the gate
unconditionally mandatory. A stronger fix (e.g. a jj `after-command` hook if/when jj
gains one, or CI-side enforcement independent of the local push path) remains future
work.
