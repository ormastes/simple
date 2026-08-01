# 364 of 413 check scripts are invoked by nothing

- **Status:** open
- **Severity:** high (verification is decorative at scale)
- **Measured at:** `a8da64469b41c084e78d1b2e509e72d925652159` (tree 109,569)
- **Date:** 2026-08-01

## Summary

A guard that no hook and no CI job runs is decoration. This repo has **413**
shell guard scripts under `scripts/check/`, `scripts/audit/`, and
`scripts/check-*.shs`. Under the most generous reachability model available,
**49 are invoked and 364 are not (88.1%)**.

The cause is structural, not incidental: the two places that list guards
(`.github/workflows/*.yml` and `scripts/hooks/pre-commit`) are **hand-maintained
lists**. Every new guard has to be remembered into them, and nothing detects the
omission. Adding a guard is easy; wiring it is a separate act nobody is forced
to perform.

## Method (reproducible)

Base commit `a8da6446`, `/usr/bin/grep` throughout (the default `grep` on this
host is ugrep and has silently disagreed on exclusion patterns).

1. Enumerate guards: tracked `scripts/{check,audit}/**.{shs,sh}` plus
   `scripts/check-*.shs` -> 413 scripts.
2. Build invocation edges `referrer -> guard-basename` two ways and take the
   UNION, so the orphan count is a conservative lower bound:
   - *narrow*: `sh|bash|source|exec <path>` and `./scripts/...` call syntax;
   - *broad*: any textual mention of the basename inside
     `scripts/ .github/ src/ bin/ tools/ config/`.
   The narrow model alone reports 383 orphans. It is wrong in the safe
   direction: it misses the `var="$repo_root/scripts/check/x.shs"` assignment
   form, which is exactly how the pre-push hook names its three sub-guards. The
   union model is the number reported here.
3. BFS from the real roots: all 27 `.github/workflows/*.yml`, `scripts/hooks/*`,
   and `scripts/check/pre-push-conflict-tree-guard.shs` (the script that
   `setup.shs` installs as `.git/hooks/pre-push`).

Counter-check on the method itself: the first run of this analysis reported
`INVOKED=0`, because the referrer field was read from `$2` of a `git grep`
line that has no commit prefix. A reachability audit that reaches nothing is
the same vacuity failure it exists to find; the field indexing was corrected
and the sanity assertion "at least one edge originates at a root" now holds
(13 such edges).

## Result

| Class | Count |
|---|---|
| Guards total | 413 |
| Invoked from a hook or CI (transitively) | 49 |
| **ORPHANED** | **364** |

Named guards checked by request:

| Script | Verdict | Evidence |
|---|---|---|
| `check-extern-registration.shs` | **ORPHANED** | zero referrers anywhere in the tree under either edge model |
| `check-seed-parse-superset.shs` | INVOKED | real `run:` step at `.github/workflows/rust-bootstrap-multiplatform.yml:178`; also listed in `scripts/hooks/pre-commit` (see caveat below) |
| `check-no-conflict-tree-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |
| `check-no-conflict-markers-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |
| `check-tree-size-push.shs` | INVOKED | via `pre-push-conflict-tree-guard.shs` |

The full orphan list is `scripts/check/guard_wiring_optout.txt`, landed with the
wiring change that follows this audit.

## Five distinct failure modes, not one

"Tracked but not invoked" is only the first axis. All five are live here:

1. **Orphaned** — the script exists, nothing invokes it. 364 scripts.
2. **Invoked but fail-open** — an earlier finding put ~70 of 92 audited scripts
   in this class. Where a script is *both* orphaned and fail-open it is pure
   decoration: it cannot run, and would report clean if it did.
3. **Hook on disk is a stale COPY of the tracked script.** PROVED this session:
   the shared repo's `.git/hooks/pre-push` was a 2,668-byte copy **two revisions
   behind**, predating `5f1b96ad9a8` — the commit that fixed three fail-opens in
   the conflict guards. Every hardening landed this session was absent from the
   hook that actually ran.
4. **Hook invokes only some of the guards it should.** The same pre-push hook
   previously ran only the conflict-*tree* guard, so literal conflict-*marker*
   text in file content was never checked on push.
5. **Hook is tracked, hand-listed, and installed by nothing.** PROVED:
   `git grep -E '(cp|ln|install)[^|;&]*scripts/hooks'` returns **zero** hits.
   Nothing installs `scripts/hooks/pre-commit`. The `.git/hooks/pre-commit`
   actually present in the shared repo is an untracked 2,488-byte secrets
   scanner dated Jun 23. So the five guards hand-listed in
   `scripts/hooks/pre-commit` — `check-workspace-root-guard`,
   `check-ui-backend-isolation`, `check-cpu-hotloop-idiom`,
   `check-seed-parse-superset`, `check-simpleos-native-surface` — **do not run
   at commit time at all**. Four of them are also in CI, so only
   `check-simpleos-native-surface.shs` is uniquely lost; but all five run
   post-push instead of pre-commit, which is not what their comments claim.

## Root cause of axis 3: the installer copies instead of linking

`scripts/setup/setup.shs` (still, at `a8da6446`):

    cp "${guard}" "${repo_root}/.git/hooks/pre-push.new"
    chmod +x "${repo_root}/.git/hooks/pre-push.new"
    mv "${repo_root}/.git/hooks/pre-push.new" "${repo_root}/.git/hooks/pre-push"

A copy is a snapshot. It goes stale the moment the tracked guard is improved,
and nothing reports the drift. The shared repo's hook was hand-replaced with a
symlink after the incident, but **the installer that created the hazard was not
fixed**, so the next `setup.shs` run re-creates it.

**Hooks must be symlinks, never copies.**

## What full enforcement would cost

Do not read "wire all 364" as the remedy. Most orphans are heavyweight evidence
producers — QEMU boots, GPU/Vulkan/DirectX readbacks, Electron and Bun browser
bitmap captures, FPGA and RISC-V hardware gates. They cannot run on a
general-purpose CI runner and were never meant to gate a commit. The defect is
not that they are unwired; it is that **nothing distinguishes "deliberately not
a gate" from "someone forgot"**. Those two states are currently
indistinguishable, which is why `check-extern-registration.shs` could land
hardened and gate nothing.

Specifically out of scope for the wiring change: `check-extern-registration.shs
--strict` exits 1 at ~2,377 unregistered symbols. It is wired **report-only**.
That backlog is a program needing an owner, not a lane's cleanup.

## Fix

Ratchet, matching the existing `ui_backend_isolation_baseline.txt` /
`cpu_lane_hotloop_baseline.txt` convention:

- `scripts/check/check-guard-wiring.shs` enumerates every guard, computes
  reachability from hooks and CI, and FAILS on any guard that is neither
  invoked nor listed in `scripts/check/guard_wiring_optout.txt` with a reason.
- The opt-out file is seeded with today's 364 orphans — an honest baseline, not
  an amnesty. Shrinking it is the follow-up program.
- The same script asserts every installed `.git/hooks/*` is a **symlink** into
  the tree (axis 3) and that its target is tracked.

Adding a guard now wires it automatically; *skipping* one becomes the deliberate
act that needs a written justification.

## Addendum: what the wiring change actually found

Wiring surfaced two live reds. Neither is weakened or allowlisted here.

**1. `check-ui-backend-isolation.shs` fails at HEAD.** Measured at `118ad7c2`
from the repo root:

    ui_backend_isolation_baselined=563
    ui_backend_isolation_current=545
    ui_backend_isolation_new=31
    ui_backend_isolation_ok=false      (exit 1, 49 stale baseline entries)

This guard is *already* wired into `.github/workflows/repo-hygiene.yml`, so the
debt is pre-existing and CI-visible. It is also hand-listed in
`scripts/hooks/pre-commit`. That is why this change does **not** make
`setup.shs` install the pre-commit hook: installing it today would fail every
commit in the repo on an unrelated pre-existing red. The blocker is recorded
rather than absorbed. Installing the pre-commit hook requires that ratchet to
be repaired first (31 new violations to fix, 49 stale baseline lines to prune);
the hook already chains a displaced `.git/hooks/pre-commit.local` so local
secret scanning survives the switch when it happens.

**2. `check-extern-registration.shs` is wired REPORT-ONLY.** `--strict` exits 1
at ~2,377 unregistered symbols. It runs without `--strict` in `repo-hygiene.yml`
so the count is printed on every run and can be driven down. Turning on
`--strict` is a program needing an owner. Do not add an allowlist and do not
lower its vacuity bound to shrink the number.

## Verification performed

Every claim below was observed end-to-end, not inferred from a script being
present in a list.

`check-guard-wiring.shs` — 6 source-level sabotages of its own selftest (BFS
neutered, orphan set forced empty, guard enumeration neutered, edge extraction
neutered, opt-out parsing neutered, reasonless-opt-out detection neutered): all
6 caught, unmodified control green. 4 behavioural sabotages against the real
tree: planted unwired guard -> `unwired_guard=`, exit 1; hook replaced by a copy
-> `hook_is_a_copy=`, exit 1; stale opt-out for a now-wired guard ->
`stale_optout_now_wired=`, exit 1; control -> `PASS — 413 guard(s) checked, 51
invoked, 362 orphaned (all justified)`, exit 0.

Push guards — verified through a REAL `git push` against a bare remote, driven
by the installed `.git/hooks/pre-push` symlink, not by running the scripts
directly:

| Fixture | Result | Remote ref |
|---|---|---|
| conflict-marker text in file content | **BLOCKED** by `check-no-conflict-markers-push.shs` (status 1), push exit 1 | unmoved at `a8da6446` |
| healthy commit | **PUSHED**, exit 0 | advanced to `2480a100` |

The marker fixture is the axis-4 case specifically: before `5f1b96ad9a8` the
pre-push hook ran only the conflict-*tree* guard, and the tree guard passes this
fixture. It is blocked now only because the hook runs both.

Hook install — `setup.shs`'s rewritten block was executed: it preserved a
pre-existing untracked `pre-commit` as `pre-commit.local` and installed
`pre-push` as a **symlink** (`ls -l` confirmed `lrwxrwxrwx`). The chained
`.local` hook was observed firing during a real `git commit`
(`LOCAL-HOOK-RAN` in the hook output).

## Remaining debt (not fixed here)

- **362 orphans** in `guard_wiring_optout.txt`. The set can no longer grow
  silently, but shrinking it needs an owner.
- **`scripts/hooks/pre-push` is shadowed.** Its tracking checks (`check-dbs`,
  `tracking check`, `traceability-check`) never run, because `.git/hooks/pre-push`
  is the conflict guard instead. Chaining them was not attempted: they require a
  built `bin/simple` and would block pushes on a fresh clone. This is a second
  live instance of axis 4.
- **`check-guard-wiring.shs`'s reachability model is textual**, so a guard
  merely *named* in a workflow comment counts as wired. It over-approximates
  reachability on purpose -- that under-reports orphans rather than failing a
  build on a parse gap -- but it means the 51 "invoked" figure is an upper bound.
