# "oldguard" pre-push probe recursion — located search, guard added (2026-08-26)

- Severity: critical (host-hang precedent — thousands of `timeout`/`sh`
  processes spawned, box became unresponsive, user had to kill the process
  family manually on 2026-08-25)
- Status: MITIGATED (defense-in-depth guard added); exact original offending
  script NOT located

## What is known (from session memory, `oldguard-prepush-probe-recursion.md`)

On 2026-08-25 a pre-push hook probe recursed with no depth limit and no
re-entry guard, spawning thousands of `timeout`/`sh` processes and hanging
the host. The working hypothesis recorded at the time: "the probe re-enters
itself (a pre-push hook invoking something that pushes, or a guard that
shells out to the guard)". It was also noted that the probe is **not** in
`/mnt/data/worktrees/simple-main/scripts/` or its `.git/hooks/` — it lives in
another worktree.

## Search performed this session (read-only, no execution)

1. `grep -rli oldguard` across every `/mnt/data/worktrees/*` tree (`scripts/`,
   `.git/hooks/*`, and a depth-4 filename scan) — **zero hits**. "oldguard" is
   a session nickname, not a literal identifier in any tracked file.
2. Read every `pre-push`-named file in `simple-main`
   (`.git/hooks/pre-push`, `.git/hooks/pre-push.local`,
   `.git/hooks/pre-push.legacy-20260822`, `scripts/hooks/pre-push`,
   `scripts/hooks/pre-push-worktree-launcher`,
   `scripts/check/pre-push-conflict-tree-guard.shs`). None of these contain a
   `git push` / `jj git push` call that would re-trigger themselves — the
   chain is: git hook -> `scripts/hooks/pre-push` (worktree-resolving
   launcher) -> `scripts/hooks/pre-push` dispatcher -> `pre-push.local`
   (if present and different from canonical) and
   `pre-push-conflict-tree-guard.shs` -> `exec sh check-push-must-pass.shs`.
   `check-push-must-pass.shs` and `check-hook-installation.shs` were also
   read in full for `git push`/self-exec patterns — both are pure read-only
   checks (`git rev-parse`, file-mode probes, ledger reads); neither pushes
   or shells out to itself.
3. `grep -rlE '(sh "\$0"|sh \$0|source \$0|bash \$0)'` across every
   `*/scripts/check/*.shs` and `*/scripts/hooks/*` under all
   `/mnt/data/worktrees/*` — zero hits. No tracked script under those paths
   currently contains a literal self-re-exec pattern.
4. Grepped `doc/08_tracking/bug/` for `recursion`/`oldguard`/pre-push-hook
   hazards; the closest historical analogue is
   `cli_compile_delegation_fork_bomb_wrapper_2026-07-24.md` (a **different**
   bug: `simple compile --backend=vhdl` delegating to a wrapper that
   re-execs the full CLI, unrelated to git push hooks, already fixed with a
   `SIMPLE_COMPILE_DELEGATED` marker guard — the same *shape* of fix applied
   below).

**Conclusion: the exact recursing artifact from 2026-08-25 could not be
located by static search of the currently-tracked worktree trees.** It may
have lived in a since-cleaned scratch/temp lane, a locally-modified
`.git/hooks/pre-push.local` in some other lane that has since been reset, or
an ad-hoc command a session ran by hand rather than a committed script. Per
the task's own escape hatch, this is reported rather than risking the host by
attempting to execute anything that shells out to a push.

## Mitigation implemented (defense-in-depth, no execution risk)

`scripts/hooks/pre-push` (the tracked, worktree-resolving pre-push
dispatcher that every hook chain in `simple-main` ultimately reaches) now
carries an `OLDGUARD_DEPTH` re-entry sentinel plus a hard depth cap
(`OLDGUARD_MAX_DEPTH=3`):

```sh
: "${OLDGUARD_DEPTH:=0}"
OLDGUARD_DEPTH=$((OLDGUARD_DEPTH + 1))
export OLDGUARD_DEPTH
OLDGUARD_MAX_DEPTH=3
if [ "$OLDGUARD_DEPTH" -gt "$OLDGUARD_MAX_DEPTH" ]; then
    echo "pre-push dispatcher: OLDGUARD_DEPTH=$OLDGUARD_DEPTH exceeds cap ($OLDGUARD_MAX_DEPTH) — refusing, this hook (or something it calls) is re-entering itself" >&2
    exit 1
fi
```

Because the env var is exported and inherited by every child process (the
same mechanism the VHDL fork-bomb fix at
`cli_compile_delegation_fork_bomb_wrapper_2026-07-24.md` relies on), any
chain where this dispatcher — or something it calls — ends up invoking a
real `git push`/`jj git push` that re-triggers this same hook is bounded to a
handful of hops instead of growing until the box stops responding. This is
unconditional defense-in-depth: it does not depend on having found the
original 2026-08-25 offender, and it costs nothing on the non-recursive path
(one integer increment per push).

## Fixture proof (never executed a real hook, git command, or push)

Two POSIX-shell fixtures under a process cap and a hard `timeout`, proving
the guard is load-bearing rather than a no-op:

- `recursive_hook_sim.shs` — reproduces the recursion *shape* (a script that
  "invokes something that pushes, which re-triggers the same hook") using
  the exact `OLDGUARD_DEPTH` sentinel/cap logic now in
  `scripts/hooks/pre-push`. Run as
  `( ulimit -u 4000; timeout 20 sh recursive_hook_sim.shs )`: stopped itself
  at **4 invocations** (`OLDGUARD_DEPTH=4 exceeds cap (3)`, exit 1).
- `recursive_hook_sim_noguard.shs` — same shape with NO depth guard, bounded
  only by an externally-imposed test ceiling (never left unbounded, per the
  task's hard safety rule) so a regression cannot hang the host even if the
  guard were reverted. Run with `OLDGUARD_TEST_CEILING=50`: ran to **51**
  invocations, i.e. it would have kept recursing past that point with no
  guard at all — confirming the guard, not incidental behavior, is what
  bounds the chain.

Both fixtures ran under `timeout 20` and `ulimit -u 4000` in the invoking
subshell; neither touched git, jj, or any real push path.

## Residual work

If the original 2026-08-25 probe script is ever found (e.g. surfaced again
in a fresh lane), add its exact re-entry line to this record and verify the
now-exported `OLDGUARD_DEPTH` sentinel is checked on its entry path too —
the dispatcher-level guard only bounds chains that pass back through
`scripts/hooks/pre-push`; a probe that recurses through some other,
unrelated entry point (never routing back through this dispatcher) would
need its own local check of the same env var.
