# Environment guard can print PASS after Git discovery fails

Status: OPEN. Discovered during item 7 verification on Windows, 2026-10-03.

Running `sh scripts/audit/direct-env-runtime-guard.shs --working` through WSL
against a Windows-created linked worktree prints `fatal: not a git repository`
because its `.git` pointer contains a Windows path, then prints
`STATUS: PASS direct-env-runtime-guard` and exits zero. `--staged` has the same
failure. An empty path list caused by Git failure is not a successful audit.

Reproduction context: Windows worktree
`C:/dev/simple-item7-completion-20261003`, mounted as
`/mnt/c/dev/simple-item7-completion-20261003` in Ubuntu WSL. The failing command
was launched with `wsl -d Ubuntu -- sh -lc` from PowerShell. No passing audit
evidence was accepted from those invocations.

Explicit `GIT_DIR`/`GIT_WORK_TREE` translation made Git recognize the worktree,
but `git diff --name-only -- src/app src/lib/gc_async_mut` took over four minutes
on the NTFS checkout and held its index lock. The owned audit process was
terminated; no elapsed-time observation was mistaken for a terminal result.
Native Git Bash completed both guard modes successfully after that termination.

Required repair: reject failed Git path discovery before auditing any paths;
distinguish a successful empty diff from a failed producer. Regression tests
must cover an invalid repository/worktree, a successful empty diff, a compliant
change, and a forbidden added leaf runtime call. Prefer native Git for Windows
worktrees, or isolated ext4 checkouts for Linux verification. Do not claim that
native empty-diff success validates already-committed source changes.
