# Recurring silent `core.bare = true` on the shared `.git/config`

- **Date:** 2026-08-17 (investigated 2026-08-18)
- **Status:** MECHANISM PROVEN + GUARD LANDED; specific 2026-08-17 writer SUSPECTED, not caught in the act
- **Severity:** HIGH — while set, it misdirects every content-dependent push guard
- **Guard:** `scripts/check/check-core-bare-sanity.shs`

## The event

`core.bare = true` was written into `.git/config` of this NON-bare repo at least
three times on 2026-08-17, each time silently. Effects:

- Every working-tree git command fails `fatal: this operation must be run in a
  work tree`, despite an intact ~115,000-file working tree. **This is not a tree
  wipe** and was initially misdiagnosed as one.
- Worse, it silently MISDIRECTS the pre-push guards: `git rev-parse
  --is-inside-work-tree` is false in every worktree, so guards either exit 2 or
  resolve a different toplevel and report clean on a tree nobody is pushing.
  `pre-push-conflict-tree-guard.shs` was taught to detect it and refused one
  lane's push (`a stray core.bare in .git/config misdirects every guard`);
  before that hook existed, guards ran and reported on the wrong thing.

Repair each time: `git config core.bare false`.

---

## PROVEN

### 1. The write mechanism, reproduced on demand (git 2.43.0)

`git init <somedir>` with an **inherited `GIT_DIR`** re-initialises the repo
`GIT_DIR` names. When `GIT_DIR` ends in a slash or in `/.`, git cannot infer an
adjacent work tree and writes `core.bare = true` into the victim's config.
Measured in a throwaway repo:

| inherited GIT_DIR | victim `core.bare` after `git init <tmp>` |
|---|---|
| unset | false |
| `<abs>/.git` | false |
| `<abs>/.git/` (trailing slash) | **TRUE** |
| `<abs>/.git/.` | **TRUE** |

`git -C <dir>` does **not** override an inherited `GIT_DIR`, so a fixture
builder that looks local is not. This is the same mechanism already documented
for the 2026-08-01 incident
(`doc/08_tracking/bug/push_guard_selftest_escapes_into_shared_repo_2026-08-01.md`),
which was fixed only in `check-tree-size-push.shs`.

Shipped as fixture 6 of the new guard's `--selftest`, so it is re-proved on
every run rather than asserted from memory.

### 2. The stated suspect is RULED OUT

`git worktree add` racing background auto-packing / gc does **not** do this. In
a throwaway repo carrying **200 stale worktree entries**, 40 concurrent rounds
of `git worktree add --detach` + `git gc --auto` + `git repack -ad` + `git
worktree prune` (120 racing processes) left `core.bare = false` every time.
`git worktree add` under a hostile trailing-slash `GIT_DIR` also left it false —
only `git init` flips it.

### 3. Origin file, and no repo-authored *setter*

`git config --list --show-origin` supplies `core.bare=false` from
**`file:.git/config`** — the shared config, not a worktree config. The repo does
use `extensions.worktreeConfig=true` with `.git/config.worktree`, but that file
holds only `core.sparsecheckout` / `core.sparsecheckoutcone`; it never carries
`core.bare`. No script, hook, or `.shs` anywhere under `scripts/`, `src/`,
`tools/`, or `.claude/` ever *sets* `core.bare` — every hit is a guard reading
it or a comment describing this pathology. So the write is a **side effect**,
never an intentional assignment. Git itself is not "to blame" either: it is
doing exactly what a re-init under a relocated `GIT_DIR` means.

---

## SUSPECTED (not proven — the writer was not caught in the act)

Six scripts build `git init` fixtures **without stripping `GIT_DIR`**, and are
therefore live instances of the proven mechanism. Any of them, run from a shell
in the mandated plumbing-landing flow (which exports `GIT_DIR`), would flip
`core.bare` exactly as observed:

- `scripts/check/check-dangling-references.shs`
- `scripts/check/check-fix-has-two-specs.shs`
- `scripts/check/check-engine-claiming-specs-use-probe.shs`
- `scripts/check/check-engine-claiming-specs-use-probe-delta.shs`
- `scripts/check/check-rules-sdl-integrity.shs`
- `scripts/check-workspace-root-guard.shs`

This is a strong hypothesis, not a proof: no logging ties a specific run to a
specific flip. **Proposed fix (not applied here):** give each of these the
`ST_ENV_STRIP` treatment already in `check-tree-size-push.shs` — strip every
relocating `GIT_*` and pass fixture identity per-process via `-c`, so no config
file is ever written. That is the actual root-cause repair; the guard below is
only detection.

---

## The guard

`scripts/check/check-core-bare-sanity.shs` — read-only, no locks, no object
walks, milliseconds, safe to call from other guards.

Fails only on a **provable contradiction**: common git dir basename is `.git`,
its parent holds a checkout, and `core.bare` is true. A genuinely bare repo
(`foo.git/`) does not match and is never failed. Verdicts: `PASS — <n> ...
checked` exit 0 / `FAIL` exit 1 / `ERROR — nothing was checked` exit 2; a
0-repository run is ERROR, never a pass. `--selftest` is fatal and runs before
every real scan — 6 fixtures, including the required `core.bare=true` fixture
that MUST fail and the live trailing-slash reproduction.

Measured: selftest `PASS — selftest fixtures checked` (6/6); real repo `PASS — 1
repository checked, core.bare is false/unset on non-bare layout`; a non-repo
directory `ERROR — nothing was checked` exit 2.

---

## Worktree census (census only — nothing removed)

| metric | value |
|---|---|
| `.git/worktrees/` admin entries | 402 |
| registered by `git worktree list` | 403 (incl. the main checkout) |
| gitdir targets still present on disk | 400 |
| gitdir targets pointing at DELETED paths | 2 |
| reported `prunable` by git | 0 |
| `.git/worktrees/` disk | 5.6 GB |
| `.git` total | 55 GB |
| admin entries older than 24h | 0 |
| leftover `branch.worktree-agent-*` config stanzas | 70 |

Roots: 112 under `/mnt/data/worktrees`, 97 under `/home/ormastes/dev`, 31 under
`/mnt/data/tmp`, 12 under `/mnt/data/bs2`, plus scattered `/tmp/tmp.*`
seed-worktrees.

The "~392 stale worktrees" framing is **not what the data shows**: only 2 of 402
point at deleted paths, git considers 0 prunable, and *every* admin entry is
under 24h old. These are overwhelmingly LIVE trees belonging to concurrent agent
lanes, not stale debris. They are also **not** the cause — the race hypothesis
was disproved above.

### Proposed cleanup — NOT EXECUTED, and deliberately so

Standing user rule: never remove worktrees during a deploy/bootstrap; archive
and report candidates, never reap mid-bootstrap. A bootstrap lane may be active,
so removal is out of scope. When a maintainer confirms no lane is live:

1. `git worktree prune --dry-run -v` first, and read it — expect ~2 entries.
2. Only then `git worktree prune`.
3. Separately, garbage-collect the 70 orphaned `branch.worktree-agent-*` config
   stanzas whose branches no longer exist (`git config --unset-all` per
   stanza) — cosmetic, but they are what makes `.git/config` unreadable and
   made a stray `bare = true` line easy to miss by eye.
4. The 5.6 GB in `.git/worktrees` is mostly live per-worktree indexes; it is not
   recoverable without removing live trees. Do not chase it.

Do **not** run `git gc` / `git prune` / `git repack` on the shared repo while
lanes are active. The repo reports "too many unreachable loose objects" (a
known 2026-08-01 side effect of the same fixture-escape class), but a repack
during ~15 concurrent lanes' operations is its own hazard.

## Follow-up

- [ ] Apply `ST_ENV_STRIP` to the six unfixed `git init` fixture builders above.
- [ ] Wire `check-core-bare-sanity.shs` into `pre-push-conflict-tree-guard.shs`
      as the canonical implementation, replacing that hook's inline copy.
