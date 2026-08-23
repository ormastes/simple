# Pre-push guard chain is unreachable for every detached-HEAD lane (2026-08-23)

**Status: OPEN. Severity: HIGH — this is not one lane's push failing, it is the
entire guard chain being structurally unreachable for the whole lane fleet.**

## Symptom

Every push from a detached-HEAD worktree aborts with:

```
check-hook-installation: PASS — 10 check(s) performed, hook wiring intact
push-must-check: FAIL — no pushed refs were provided
error: failed to push some refs to 'https://github.com/ormastes/simple.git'
```

Note the first line: the wiring guard passes and reports the chain intact. The
chain *is* intact. It is being fed nothing.

## Mechanism (this is the part previous reports lacked)

Git supplies the pre-push hook its ref lines **on stdin**. The chain is
launcher -> `scripts/hooks/pre-push` (`cat > "$REFS"`) -> canonical guard ->
`exec sh check-push-must-pass.shs`, which does:

```
cat > "$_refs"                                   # check-push-must-pass.shs:324
[ -s "$_refs" ] || die "no pushed refs were provided"   # :325
```

`$REFS` is empty because **git sends no ref lines for a SHA-source refspec
pushed from a detached HEAD**. Nothing in the chain consumes stdin; verified by
grep — the dispatcher forwards it with `< "$REFS"` and the canonical guard neither
reads nor redirects it before `exec`.

Reproduced 3x on 2026-08-23 in `/mnt/fast/wt/use-resolve-1`:

| push form | HEAD state | result |
|---|---|---|
| `git push origin <sha>:refs/heads/main` | detached | FAIL, empty `$REFS` |
| `git push origin HEAD:refs/heads/main`  | detached | FAIL, empty `$REFS` |
| same, after a clean rebase onto origin  | detached | FAIL, empty `$REFS` |

The third row matters: it rules out the non-fast-forward explanation. It fails
identically when the push *is* a clean fast-forward.

## Why this is structural, not incidental

Lanes that push successfully do so from a **real local branch**. In this session
every lane works **detached on purpose**, because `main` is checked out in
`/mnt/data/worktrees/simple-main` and a linked worktree cannot check out a branch
that is already checked out elsewhere. So the working configuration is
unavailable to the fleet by construction, and the guard chain — conflict-tree,
tree-size, markers, divergence, seed-build, runtime-API, wiring — is reachable
for **none** of them.

The failure mode is the dangerous direction: it does not silently pass, it
blocks. But its practical effect is that every lane is pushed toward
`--no-verify`, which skips ALL guards rather than the one that is broken. A
guard chain that is routed around on every push protects nothing — the same
reasoning `check-seed-builds-push` used when it deleted its own fail-open path
filter on 2026-08-18.

## Proposed fix

1. **Fall back to deriving the refs when stdin is empty.** The hook receives the
   remote name and URL as `$1`/`$2`, and the refspec is recoverable from
   `HEAD` plus the push destination. When `$_refs` is empty, synthesise the
   line from `git rev-parse HEAD` and the configured/passed destination rather
   than dying.
2. **Distinguish "cannot determine" from "nothing to push".** Per this repo's
   own verdict convention, an undetermined input is `ERROR — nothing was
   checked` (exit 2), not `FAIL` (exit 1). Today the two are conflated, which is
   why the message reads like a user error instead of a harness defect. Treat
   "no refs AND no fallback" as ERROR.
3. **Add a fixture** to the guard's selftest that invokes it with empty stdin and
   asserts the fallback fires — otherwise this regresses silently.

## Cross-references

- A sibling lane independently reported the same failure at the same line today;
  this record supplies the mechanism (sha-source refspec + detached HEAD) that
  report lacked. Consolidate rather than tracking two.
- This is the **fourth** push-path outage recorded on 2026-08-23.
- Related, but a DIFFERENT bug found in the same session:
  `check-guard-wiring.shs` builds its graph by grepping guard basenames out of
  file CONTENT including `#` comments, so a new guard that merely *cites* a
  sibling in prose marks it wired. Measured: `0 stale` pristine vs `3 stale`
  with the citation, delta exactly the four characters `.shs`. Reproduction at
  `/mnt/data/tmp/handoff/guard_wiring_comment_phantom_edge.md`.

## Interim workaround

Push with `--no-verify` (sanctioned by standing user authorization as of
2026-08-23) and record every guard verdict in the commit message, explicitly
labelled as manually run — the committer's assertion, not the hook's.
