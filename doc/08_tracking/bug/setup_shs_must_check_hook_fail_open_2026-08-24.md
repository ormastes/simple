# General setup skips or weakens mandatory must-check hooks

Status: fixed; manually unverified by user instruction

## Reproduction

On 2026-08-24, a fresh linked-worktree fixture reported `.git` kind `file` and
the current `scripts/setup/setup.shs` gate (`[ -d "$repo_root/.git" ]`) reported
`setup_gate=skipped`. Source inspection also found:

- the generic setup loop pre-moves both `pre-commit` and `pre-push`, bypassing
  the dedicated pre-push installer's canonical/local-hook classification;
- `install-must-check-hooks.shs --install || true` discards installation
  failure; and
- `check-hook-installation.shs` failure is reduced to a warning.

The dedicated Unix installer already resolves the shared hooks directory and
handles linked worktrees safely. General setup must delegate pre-push ownership
to it, propagate installation and verification failures, and work when `.git`
is either a directory or a linked-worktree indirection file.

## Acceptance

- A linked-worktree fixture enters the general setup hook path.
- General setup never pre-moves `pre-push`; the dedicated installer alone owns
  preservation/replacement.
- Missing installer, failed install, or failed wiring verification makes setup
  fail nonzero.
- Existing pre-commit deferral behavior remains unchanged.
- Unix dedicated-install and Windows TODO/evidence contracts remain unchanged.
