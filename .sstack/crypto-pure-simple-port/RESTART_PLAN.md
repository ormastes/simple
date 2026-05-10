# Restart Runbook

Use this as the operator restart checklist for the next 1-2 sessions. Keep
`state.md` as the canonical feature-status and acceptance-criteria ledger, and
keep `research/w_head_triage.md` as the canonical consolidation-strategy
reference.

## Live Repo Facts

- `HEAD` is detached at `d43e8c5c50`.
- `main` is `eb6db72ba3`.
- `origin/main` is `f3fce25c8e`.
- `main` is ahead of `origin/main`; use `main` as the consolidation line.
- `.git/index.lock` is currently present and is the first safety gate.

## Recovery Inputs

Use only these artifacts to restart safely:

- Status / acceptance ledger: `.sstack/crypto-pure-simple-port/state.md`
- Milestone ledger: `.sstack/crypto-pure-simple-port/research/m_status.md`
- Consolidation strategy: `.sstack/crypto-pure-simple-port/research/w_head_triage.md`
- Recovery branches:
  - `worktree-wa-bignum` at `a53f8b4ec1`
  - `worktree-wb-fields` at `ddec12003d`
  - `worktree-wz-fe-invert` at `1e4817a8f1`
- Recovery notes still worth consulting:
  - `.sstack/crypto-pure-simple-port/impl/wa_bignum_recover_done.md`
  - `.sstack/crypto-pure-simple-port/impl/wb_fields_recover_done.md`
  - `.sstack/crypto-pure-simple-port/impl/wz_fe_invert_triage_done.md`

Ignore the old branch-by-branch archaeology here; refer to the ledgers above if
deeper forensics are needed.

## Ordered Restart Procedure

1. Inspect `.git/index.lock` first.
   - Check age and active holder.
   - Minimal check sequence:
   ```bash
   ls -l --time-style=long-iso .git/index.lock
   lsof .git/index.lock
   ```
   - Clear it only if it is stale and unowned.
   - Do not run further `git` / `jj` recovery steps until this is resolved.
2. Confirm the repo positions exactly.
   - `HEAD` must still be detached at `d43e8c5c50`.
   - `main` must still be ahead of `origin/main`.
   - Re-check with:
   ```bash
   git rev-parse --short=10 HEAD
   git rev-parse --short=10 main
   git rev-parse --short=10 origin/main
   git status --short --branch
   ```
   - Re-check the exact `HEAD`, `main`, and `origin/main` SHAs before making
     recovery moves.
3. Adopt Strategy D from `research/w_head_triage.md`.
   - `main` is the consolidation branch.
   - Do not create a new long-lived integration branch.
   - Treat detached `HEAD` as stale recovery state, not the line to continue on.
   - Re-run the non-destructive guard before any push:
   ```bash
   FC_LOCAL=$(git ls-tree -r main | wc -l)
   FC_REMOTE=$(git ls-tree -r origin/main | wc -l)
   echo "delta: $((FC_LOCAL - FC_REMOTE))"
   git diff --name-only --diff-filter=D origin/main..main
   ```
   - If the delta is negative or the deletion list is non-empty, stop.
4. Validate the runner before trusting any spec result.
   - Run the explicit red probe:
   ```text
   echo 'use std.spec
   describe "probe": it "fail": expect(1).to_equal(2)' > /tmp/probe.spl
   bin/simple test /tmp/probe.spl
   ```
   - The probe must fail with one failed test.
   - If it passes, stop. All earlier green results on this line are untrusted.
5. Recover the missing crypto math files before more crypto work.
   - Restore the bignum files from `worktree-wa-bignum`.
   - Restore the field files from `worktree-wb-fields`.
   - Pull `worktree-wz-fe-invert` only for the triage/doc input it still
     contributes.
   - Validate recovery by checking both file presence and file count/content of
     the restored math modules.
   - Minimum validation:
   ```bash
   git diff --stat main..worktree-wa-bignum -- src/lib/common/math/bignum
   git diff --stat main..worktree-wb-fields -- src/lib/common/math/field
   find src/lib/common/math/bignum src/lib/common/math/field -type f | sort
   ```
6. Re-run all suspect wave-3 through wave-6 crypto claims under the restored
   runner.
   - Re-run previously reported green KAT/spec results.
   - Do not trust any earlier pass recorded from the broken detached-HEAD path
     until it re-passes now.
7. Continue feature work only after steps 1-6 are clean.

## Immediate Priorities

### P0

- Repo safety: resolve `.git/index.lock` correctly.
- Runner truthfulness: red-probe must fail correctly.
- Recover missing bignum and field files from the recovery branches.
- Re-run the suspect verification set and replace any false-green assumptions.

### P1

- Replace `mod_inv_ct_stub` and `mod_exp_ct_stub` with real implementations.
- Then continue SSH M1 modern advert/login work on the restored math base.

## After Restart

Defer these until the restart path above is complete:

- TLS 1.3 M3 broader implementation work.
- Curve-layer unification / wider crypto cleanup beyond the immediate stub
  replacements.

## Canonical References

- Acceptance criteria and feature status: `.sstack/crypto-pure-simple-port/state.md`
- Milestone status ledger: `.sstack/crypto-pure-simple-port/research/m_status.md`
- Consolidation strategy: `.sstack/crypto-pure-simple-port/research/w_head_triage.md`
