# Working-tree environment guard can hide a failed Git inventory

Status: open; discovered while preparing node-attribute structural verification.
Scope: `scripts/audit/direct-env-runtime-guard.shs`, `--working` path enumeration.
Source baseline: `6e03930143983a5c9861321f67aff300b07f16ed` on `release/1.0.0`.

The working-tree guard runs `git diff --name-only -- src/app src/lib/gc_async_mut`
inside a grouped inventory pipeline before scanning the selected files. During
this session the MSYS Git child remained in index refresh holding the isolated
worktree's optional `index.lock`. That exact audit-owned child was terminated
after its command/parent were verified. The guard nevertheless exited zero and
printed `STATUS: PASS direct-env-runtime-guard`.

That interrupted result was rejected as verification evidence. After the Git
process was confirmed terminal, its empty stale lock was removed only from this
isolated worktree. The guard was rerun unchanged with native Git first on PATH
and `GIT_OPTIONAL_LOCKS=0`; that uninterrupted run passed. The staged run also
passed independently.

Expected: any failed Git inventory makes the guard fail or explicitly report
incomplete coverage, rather than treating a missing set of paths as clean.
The eventual repair should retain Git status before filtering/combining lists
and add a regression with a Git shim that fails `diff` but succeeds `ls-files`.
It must not accept an empty or partial inventory as PASS. No guard implementation
change or regression-test execution is claimed in this report.
