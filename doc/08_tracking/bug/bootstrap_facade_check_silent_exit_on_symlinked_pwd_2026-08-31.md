# bootstrap-from-scratch.sh exits 1 silently when invoked from a symlink-aliased PWD

- Date: 2026-08-31
- Severity: medium (blocks bootstrap with zero diagnostic output)
- Status: OPEN (workaround documented; script not changed)

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
exits rc=1 with **no output at all** (stdout and stderr both empty), when the
shell's logical `$PWD` is `/home/ormastes/dev/pub/simple` (a symlink alias of
the physical repo root `/mnt/data/worktrees/simple-main`).

## Root cause (traced with `sh -x`)

The script derives `repo_root` with logical `pwd` (giving the `/home/...`
alias) and then sources `scripts/check/lib/bootstrap-stage3-provenance.shs`.
That facade sets `bootstrap_stage3_facade_dir` via `pwd -P` (physical) and
compares it against `BOOTSTRAP_STAGE3_FACADE_PATH` built from the logical
root:

```
+ [ /home/ormastes/dev/pub/simple/scripts/check/lib/bootstrap-stage3-provenance.shs = /mnt/data/worktrees/simple-main/scripts/check/lib/bootstrap-stage3-provenance.shs ]
+ return 1
```

The mismatch returns 1 with no message, and `set -e` kills the whole
bootstrap silently.

## Workaround

Invoke from the physical path: `cd -P /mnt/data/worktrees/simple-main` first.

## Suggested fix

Either canonicalize both sides with `pwd -P` before comparing, or emit a
typed error line (`bootstrap-policy-error: facade-path-alias-mismatch ...`)
before returning, per the repo's fail-with-verdict convention.
