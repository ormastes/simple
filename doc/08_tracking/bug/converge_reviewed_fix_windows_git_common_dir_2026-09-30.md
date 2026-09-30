# Reviewed-fix convergence: Windows common Git directory

## Failure and requirement

Preparing the reviewed NUL-concat backport from a linked Windows worktree
failed before fetch or worktree creation. `git rev-parse --git-common-dir`
returned `C:/Users/ormas/dev/simple/.git`, and the helper incorrectly tried to
enter `/d/dev/simple-astra-nul-concat-release-20260930/C:/Users/ormas/dev/simple/.git`.

REQ-001: preserve absolute POSIX, drive-rooted, and UNC common Git paths,
including Windows backslash spellings. Prefix relative paths with the
coordinator root; a drive-relative spelling such as `C:relative/.git` remains
relative. Preserve the existing physical-directory resolution and protected
convergence checks.

## Correction and design

`scripts/release/converge-reviewed-fix.shs` now passes the Git result through
`resolve_git_common_dir` before resolving its physical directory. Its small
case expression accepts the same absolute path forms as the existing hook
checker. That checker has no reusable sourceable path module, so this change
does not introduce a dependency on its executable validation entrypoint.

The new `--selftest-paths` mode exercises the production resolver directly.
The existing focused checker runs that mode and uses a real linked
coordinator for its backport case. This reproduces the absolute common Git
directory returned by Git for Windows while retaining the real temporary
repository, remote, cherry-pick, and preparation-receipt assertions.

## Verification

One focused cycle passed under `C:/dev/tool/Git/bin/bash.exe`:

`sh scripts/check/check-converge-reviewed-fix.shs`

The nine resolver cases cover POSIX absolute, drive forward-slash,
drive backslash, lowercase drive with spaces, UNC forward-slash, UNC
backslash, relative `.git`, relative parent traversal, and drive-relative
paths. The integration checks cover backport from a linked coordinator,
forward-port, unchanged protected refs, receipt binding, rejected duplicate
or negative reviews, dirty coordinators, and cleanup after a rejected
receipt path.

UNC spelling is covered by the production resolver test; the test does not
claim connectivity to a real network share. Existing physical path and
ownership checks still run after resolution.

The NUL-concat release preparation can resume after this helper change is
available. Its release push remains separately blocked by the interpreter
registry gap. The registry lane's exhausted verification cycles, full
bootstrap checks, and production release admission were not rerun or
represented as passing by this focused helper test.
