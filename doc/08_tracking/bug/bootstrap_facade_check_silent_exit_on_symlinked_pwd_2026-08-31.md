# bootstrap-from-scratch.sh exits 1 silently when invoked from a symlink-aliased PWD
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Triage 2026-11-03 (boot-script-fixes lane)

Already fixed on origin: scripts/check/lib/bootstrap-stage3-provenance.shs:31-33 now prints a typed message naming the non-canonical facade path and the physical-path remedy before returning 1. Row closed fixed.

## Triage 2026-11-10 (p3-boot2 lane)

SUPERSEDED — the 2026-11-03 triage's claim is verified live on
work/p3-boot2-20261110 (base origin/release/1.0.0). The silent-exit defect is
fixed: `scripts/check/lib/bootstrap-stage3-provenance.shs:31-33` now prints a
typed diagnostic naming the non-canonical facade path, the expected canonical
path, and the physical-path remedy before returning 1.

Live reproduction (this lane, one cycle): sourcing the facade with a
non-canonical path component (`scripts/check/lib/../lib/bootstrap-stage3-provenance.shs`,
the same string-compare arm a symlinked PWD hits — no Windows symlink
privilege needed) prints

    bootstrap Stage 3 provenance: facade path is not canonical: <given> (expected <physical>; invoke through the physical path, not a symlink such as /tmp on macOS)

and exits rc=1. No silent `set -e` death. The doc's suggested fix (typed error
line per the fail-with-verdict convention) is exactly what shipped.
