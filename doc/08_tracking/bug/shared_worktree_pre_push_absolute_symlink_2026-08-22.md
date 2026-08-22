# Shared worktree pre-push hook was bound to the last installer's checkout

**Status:** RESOLVED (`/root`, must-check tiering, 2026-08-22)

## Exact failure

Linked Git worktrees share the common repository hooks directory. The Unix
installer wrote `pre-push` as an absolute symlink to
`<installing-worktree>/scripts/hooks/pre-push`. A push from any sibling then
failed `check-hook-installation.shs` because the shared hook resolved into the
wrong worktree. The production failure and the pre-fix two-worktree regression
both reported:

```text
pre-push hook resolves to '<other-worktree>/scripts/hooks/pre-push'
```

## Root cause and fix

The hook directory is common state, while the dispatcher is worktree-relative
policy. A shared absolute symlink cannot represent both. The installer now
places a byte-stable `pre-push-worktree-launcher` in the common hook directory.
At invocation it resolves the active `git rev-parse --show-toplevel` and execs
that worktree's tracked dispatcher. The verifier accepts only the canonical
guard, tracked dispatcher, tracked launcher, or an exact launcher copy.

Legacy guard and dispatcher installs are replaced as canonical payloads rather
than preserved as `pre-push.local`; preserving an old dispatcher would recurse.
The PowerShell installer uses the same launcher contract.

## Evidence

`sh test/01_unit/scripts/must_check_tiering_test.shs` creates two linked
worktrees sharing one hook directory, installs from the first, and validates
both installer freshness and production wiring from the second. Before the fix
it failed exactly as above. After the fix it passed, and the real push subpath
reported `selftest=4s ref-path=0s installed-hook=1s` after rebase, within the
ten-second budget.

Adjacent coverage retains unrelated-hook preservation and exact legacy-payload
replacement. Windows uses the same content-addressed launcher but still needs
a native PowerShell execution row before cross-host completion is claimed.
