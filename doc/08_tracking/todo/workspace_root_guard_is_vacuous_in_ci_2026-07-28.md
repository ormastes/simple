# TODO: the workspace root guard cannot fail in CI (vacuous gate)

- **Filed:** 2026-07-28
- **Status:** open, needs design (do not hack)
- **Component:** `scripts/check-workspace-root-guard.shs`,
  `.github/workflows/repo-hygiene.yml`, `scripts/check/check-repo-hygiene.shs`

## Symptom that led here

Root-level scratch (`probe_case4.spl`, `tmp_hm_*.spl` x6) sat in `main` for
multiple commits while both the pre-commit hook and the CI hygiene job were
green. It was deleted on 2026-07-28, but the reason it survived is unfixed.

## Two independent holes

### 1. Pre-commit hook is bypassed by git plumbing

`scripts/check/check-repo-hygiene.shs:107` runs
`check-workspace-root-guard.shs audit --staged`, wired as a pre-commit hook.
Sessions in this repo routinely land changes with
`read-tree` / `update-index` / `write-tree` / `commit-tree` / `push`, which
never runs a hook. Those commits are invisible to the guard.

### 2. The CI invocation is vacuous — this is the bigger one

`.github/workflows/repo-hygiene.yml` runs the guard with no flags, i.e.
non-strict. In non-strict mode every violation class is suppressed for paths
that are already tracked:

```awk
if (strict == 1 || !tracked[first])   # WRG001
if (strict == 1 || !tracked[rel])     # WRG002 / WRG003
```

`list_audit_paths` feeds it `git ls-files` plus
`git ls-files --others --exclude-standard`. A CI checkout has no untracked,
non-ignored files. So in CI **every** candidate path is tracked, every
violation is grandfathered, and the job cannot fail regardless of what is
committed.

Verified 2026-07-28: `audit --path-file` over the then-current root scratch
(`probe_case4.spl`, `tmp_hm_capture.spl`, `tmp_hm_step1.spl`, `probes`,
`scratchpad`, `probes/x.spl`, `scratchpad/y.spl`) exits **0 / "OK"**, even
though none of those are declared in root `FILE.md`.

Corollary: the 22 `WRG002` violations seen locally on 2026-07-28 were all
**untracked** `.spipe/<slug>/` session-state dirs. They existed only in this
workstation's working copy, never in CI. Local-only noise, not a CI failure.

## Why the obvious fix does not work as-is

Adding `--strict` to the CI step makes the gate real but fails instantly on
pre-existing grandfathered debt: `probes/` (24 tracked files, referenced from
`src/lib/gc_async_mut/gpu/engine2d/font_owner.spl` and
`doc/07_guide/compiler/backends/freestanding_safe_channels.md`), `scratchpad/`
(120 tracked files, referenced from several `src/compiler/**` comments and
`.claude/skills/cert_grade.md`), and ~400 tracked `.spipe/<slug>/` dirs.

## Proposed design (needs a decision before implementing)

1. **Baseline ratchet**, mirroring the existing precedent
   `scripts/check/ui_backend_isolation_baseline.txt`: record today's strict
   violations in `scripts/check/workspace_root_baseline.txt`, run CI with
   `--strict`, and fail only on entries not in the baseline. Baseline shrinks
   over time, never grows.
2. **Range-based push guard**, mirroring
   `scripts/check/check-no-conflict-tree-push.shs`: audit
   `main@origin..@-` with `--path-file` built from `git diff --name-only`, so
   plumbing-landed commits are covered at push time rather than commit time.

(1) closes hole 2; (2) closes hole 1. Either alone leaves the other open.

## Related loose ends found while investigating

- `CLAUDE.md` / `.claude/rules/structure.md` reference
  `doc/07_guide/workspace/file_manifest.md`, which **does not exist**. The
  manifest mechanism is undocumented outside the script itself.
- `.gitignore:14` ignores `/scratchpad/`, yet 120 `scratchpad/` files are
  tracked (tracked files override `.gitignore`). Left alone deliberately —
  untracking them would break the `src/**` and skill references above — but the
  ignore rule and the tracked content contradict each other.
